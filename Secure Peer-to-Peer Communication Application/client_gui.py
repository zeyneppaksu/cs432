import tkinter as tk
from tkinter import messagebox, simpledialog, filedialog, ttk,scrolledtext
from crypto_utils import verify_signature,load_rsa_public_key
import socket
import hashlib
from Crypto.Cipher import PKCS1_OAEP
from Crypto.Random import get_random_bytes
from Crypto.Hash import SHA256
from Crypto.Util.Padding import unpad, pad 
import random
import threading
import math
from Crypto.Cipher import AES
import json # For saving/loading credentials
import os   # For checking if credentials file exists
from crypto_utils import generate_ecdh_keypair, derive_session_key, hmac_sha256, shake128_expand, update_iv
from Crypto.Cipher import AES
import hmac
from Crypto.Hash import HMAC
from Crypto.PublicKey import ECC
   
        
#  Constants 
AES_BLOCK_SIZE = 16
ID_LEN = 5 
KI_LEN = 16
N1_LEN = 16 
SID_LEN = 16


# Plaintext and Ciphertext lengths for C1 (KI || IDA || IDB || N1)
C1_PLAINTEXT_LEN = KI_LEN + ID_LEN + ID_LEN + N1_LEN 
C1_CIPHERTEXT_LEN = math.ceil(C1_PLAINTEXT_LEN / AES_BLOCK_SIZE) * AES_BLOCK_SIZE

# Plaintext and Ciphertext lengths for C2 (KI || IDA)
C2_PLAINTEXT_LEN = KI_LEN + ID_LEN
C2_CIPHERTEXT_LEN = math.ceil(C2_PLAINTEXT_LEN / AES_BLOCK_SIZE) * AES_BLOCK_SIZE

CREDENTIALS_FILE = "client_credentials.json" # File to store user credentials

# For ECDH public key message detection (heuristic)
# ECC P-256 public key (DER format) is typically 91 bytes. HMAC-SHA256 is 32 bytes.

ECDH_PUB_KEY_DER_LEN = 91 # Approx length of P-256 public key in DER
HMAC_SHA256_LEN = 32
ECDH_MSG_LEN = ECDH_PUB_KEY_DER_LEN + HMAC_SHA256_LEN 
ACK_MSG_BASE_LEN_MAX = 10 # "BAD HMAC" is 8, "ACK" is 3
ACK_MSG_TOTAL_LEN_MAX = ACK_MSG_BASE_LEN_MAX + HMAC_SHA256_LEN



 #----------------------------------------------------------------------------------
                #GUI SETUP AND UI ELEMENTS 
 #----------------------------------------------------------------------------------
class ClientGUI:
    
    """
        GUI client for secure communication.
    - Load server RSA keys
    - Connect/disconnect from the server
    - enrollment 
    - Run authentication protocol
    - Delete an existing account
    - Animated ocean-themed UI elements for funnnn!!!! umarim problem degildir
    """
    
    def __init__(self, master):
        self.master = master
        master.title("🐠 Secure Submersible Client 🐠") 
        master.geometry("1120x800") 
        master.configure(bg="#cceeff")  

        self.enc_pub_key = None 
        self.sign_pub_key = None
        self.KM = None
        self.IV = None
        self.student_id = None
        self.username = None
      
        self.peer_username_for_session = None          

        self.N1 = None
        self.N2_local = None
        self.KI = None # Integrity Key from Step 2
        self.c2_from_server = None
        self.sid_from_server = None
        self.peer_id_for_session = None
        self.peer_target_port_for_session = None
        self.conn = None 
        self.auth_success = False 

        # ECDH and Session Key related attributes (Step 3)
        self.ec_priv_key = None # Own ECC private key
        self.ec_pub_key = None  # Own ECC public key object
        self.peer_ec_pub_key_bytes = None # Peer's ECC public key (bytes)
        self.KS = None          # Shared Session Key (derived from ECDH)
        # Communication keys derived from KS
        self.EKAB = None; self.EKBA = None # Encryption keys A->B, B->A
        self.IKAB = None; self.IKBA = None # Integrity keys A->B, B->A
        self.IVAB = None; self.IVBA = None # Initial IVs A->B, B->A (will be updated per message)
        self.secure_session_active = False # Flag for active secure P2P session

        self._awaiting_n2 = False
        self._awaiting_n2_plus1 = False
        self._is_ecdh_initiator        = False   
        self._awaiting_peer_ecdh_pubkey = False   
        self._awaiting_ecdh_ack         = False   


        self.peer_listener_socket = None 
        self.peer_listener_thread_ref = None 
        self._stop_listener_event = threading.Event() 

        self.master.protocol("WM_DELETE_WINDOW", self.on_close)
        self._setup_ui() 
        self.load_credentials() 

    def _setup_ui(self):
        # --- UI Elements ---
        self.bubble_canvas = tk.Canvas(self.master, height=150, bg="#cceeff", highlightthickness=0)
        self.bubble_canvas.pack(fill="x")
        self.bubbles = []; self.bubble_tick = 0; self.fishes = []

        self.top_frame = tk.Frame(self.master, bg="#cceeff", pady=5)
        self.top_frame.pack()

        self.step_flow_label = tk.Label(self.master, text="🧭 Load Server Charts → Dive In to connect to the server → Identify Crew or Load Credentials to continue ", 
            font=("Helvetica", 10, "bold"), bg="#cceeff", fg="darkblue")
        self.step_flow_label.pack(pady=(5, 0))


        style = ttk.Style(); style.theme_use('clam')
        style.configure("TButton", padding=6, relief="flat", background="#3399ff", foreground="white", font=('Helvetica', 10, 'bold'))
        
        top_button_frame = tk.Frame(self.top_frame, bg="#cceeff"); top_button_frame.pack(pady=2)
        self.load_key_btn = ttk.Button(top_button_frame, text="🔑 Load Server Charts", command=self.load_keys); self.load_key_btn.pack(side=tk.LEFT, padx=3)
        self.connect_btn = ttk.Button(top_button_frame, text="🌊 Dive In!", command=self.connect_to_server); self.connect_btn.pack(side=tk.LEFT, padx=3)
        self.auth_btn = ttk.Button(top_button_frame, text="🐙 Identify Crew", command=self.start_auth_flow); self.auth_btn.pack(side=tk.LEFT, padx=3)
        self.delete_btn = ttk.Button(top_button_frame, text="🗑️ Delete Account", command=self.delete_account); self.delete_btn.pack(side=tk.LEFT, padx=3) 
        self.disconnect_btn = ttk.Button(top_button_frame, text="🔴 Disconnnect", command=lambda: self.disconnect_from_server(full_reset=True)); self.disconnect_btn.pack(side=tk.LEFT, padx=3) 

        middle_button_frame = tk.Frame(self.top_frame, bg="#cceeff"); middle_button_frame.pack(pady=2)
        self.ki_btn = ttk.Button(middle_button_frame, text="🗝️ Get KI", command=self.request_integrity_key); self.ki_btn.pack(side=tk.LEFT, padx=3)
        self.send_c2_sid_btn = ttk.Button(middle_button_frame, text="🗺️ Share C2||SID", command=self.send_c2_sid_to_peer); self.send_c2_sid_btn.pack(side=tk.LEFT, padx=3)
        self.change_port_btn = ttk.Button(middle_button_frame, text="⚙️ Change Sonar", command=self.change_peer_listener_port); self.change_port_btn.pack(side=tk.LEFT, padx=3)
        
        # Step 3 Buttons
        self.start_session_btn = ttk.Button(middle_button_frame, text="🚀 Start Secure Session", command=self.start_session_key_exchange)
        self.start_session_btn.pack(side=tk.LEFT, padx=3)
        self.send_secure_btn = ttk.Button(middle_button_frame, text="📧 Send Secure Message", command=self.send_secure_message_prompt)
        self.send_secure_btn.pack(side=tk.LEFT, padx=3)
        self.open_chat_btn = ttk.Button(middle_button_frame,
                                text="💬 Open Chat",
                                command=self.open_chat_window,
                                state='disabled')          # disabled until a session is live
        self.open_chat_btn.pack(side=tk.LEFT, padx=3)

        self.btn_end_session = ttk.Button(middle_button_frame, text="❌ End Session",command=self.send_end_session)
        self.btn_end_session.pack(side=tk.LEFT, padx=4)


        self.show_debug_btn = ttk.Button(middle_button_frame, text="🪼 Captain's Log", command=self.create_debug_window); self.show_debug_btn.pack(side=tk.LEFT, padx=(10,3))

        self.peer_port_label = tk.Label(self.master, text="", bg="#cceeff", fg="gray20", font=("Helvetica", 10, "italic")); self.peer_port_label.pack(anchor="w", padx=14, pady=(0, 5))
        self.peer_port = None; self.prompt_peer_listener_port()
        self.status_hint = tk.Label(self.master, text="💡 After succesfully connected: Start with 🗝️ Get KI → then 📡 Share C2||SID → then 🚀 Start Secure Session -> Ready to send secure messages!",
            font=("Segoe UI", 9, "italic"), bg="#e6f7ff", fg="black", relief=tk.GROOVE, padx=8, pady=4)
        self.status_hint.pack(fill="x", padx=12, pady=(0, 8))


        self.enrollment_status = tk.Label(self.master, text="", bg="#cceeff", fg="black", font=("Helvetica", 11, "bold")); self.enrollment_status.pack(anchor="w", padx=14, pady=(5, 0))
       
        self.msg_frame = ttk.LabelFrame(self.master, text="🌊 Ocean Voyage Log 🌊", padding=10, style="TLabelframe"); self.msg_frame.pack(padx=10, pady=5, fill="both", expand=True)
        self.msg_scroll = tk.Scrollbar(self.msg_frame); self.msg_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.msg_text = tk.Text(self.msg_frame, height=10, bg="#e0f7ff", fg="black", font=("Comic Sans MS", 10), yscrollcommand=self.msg_scroll.set, wrap="word", relief=tk.RIDGE, bd=3); self.msg_text.pack(fill="both", expand=True)
        self.msg_scroll.config(command=self.msg_text.yview)

        self.debug_window = None; self.debug_text = None; self.create_debug_window() 
        if self.debug_window: self.debug_window.withdraw()

        self.status_var = tk.StringVar(); self.status_var.set("🚢 Submarine Docked (Disconnected)") 
        self.status_bar = tk.Label(self.master, textvariable=self.status_var, relief=tk.SUNKEN, anchor=tk.W, bg="#99ccff", fg="black", font=("Segoe UI", 10, 'italic')); self.status_bar.pack(fill="x", side="bottom")

    def _update_session_ui(self):
        if self.secure_session_active:
            self.change_port_btn.state(['disabled'])
            self.open_chat_btn.state(['!disabled'])
        else:
            self.change_port_btn.state(['!disabled'])
            self.open_chat_btn.state(['disabled'])

    # Animations
    def animate_bubbles(self): 
         # Creates and starts bubble animation
        self.bubbles.clear()
        for _ in range(30):
            x = random.randint(30, self.bubble_canvas.winfo_width() - 30 if self.bubble_canvas.winfo_width() > 60 else 880)
            y = 150 
            size = random.randint(8, 18)
            speed = random.uniform(1.2, 2.4)
            wiggle = random.uniform(0.15, 0.3)
            color = random.choice(["#a0dfff", "#87cefa", "#5dade2", "#b0e0e6"])
            bubble = self.bubble_canvas.create_oval(x, y, x + size, y + size, fill=color, outline="")
            self.bubbles.append({"id": bubble, "x": x, "y": y, "size": size, "speed": speed, "wiggle": wiggle})
        self.bubble_tick = 0
        self.move_bubbles()

    def move_bubbles(self): 
         # Animates bubbles moving upwards
        self.bubble_tick += 1
        for bubble in self.bubbles[:]:
            bubble['y'] -= bubble['speed']
            wobble = math.sin(self.bubble_tick * bubble['wiggle']) * 2
            x1 = bubble['x'] + wobble; y1 = bubble['y']
            x2 = x1 + bubble['size']; y2 = y1 + bubble['size']
            try:
                if self.bubble_canvas.winfo_exists():
                    self.bubble_canvas.coords(bubble['id'], x1, y1, x2, y2)
                    if y2 <= 0:
                        self.bubble_canvas.delete(bubble['id'])
                        self.bubbles.remove(bubble)
            except tk.TclError: 
                if bubble in self.bubbles: self.bubbles.remove(bubble)
        if self.bubbles and hasattr(self.master, 'winfo_exists') and self.master.winfo_exists():
            self.master.after(30, self.move_bubbles)
            
    def animate_fishes(self): 
        # Creates and starts fish animation
        self.fishes = []
        self.fish_tick = 0
        canvas_width = self.bubble_canvas.winfo_width() if self.bubble_canvas.winfo_width() > 0 else 850
        for _ in range(8):
            x = random.randint(0, canvas_width - 50 if canvas_width > 50 else 800)
            y = random.randint(30, 130)
            body_length = random.randint(30, 50); body_height = body_length // 2
            speed = random.uniform(1.0, 2.0); wiggle = random.uniform(0.05, 0.2)
            color = random.choice(["#ffa07a", "#ff6347", "#ff8c00", "#f08080"])
            body = self.bubble_canvas.create_oval(x, y, x + body_length, y + body_height, fill=color, outline="")
            tail = self.bubble_canvas.create_polygon(x, y + body_height // 2, x - 10, y, x - 10, y + body_height, fill=color, outline="")
            self.fishes.append({"body": body, "tail": tail, "x": x, "y": y, "w": body_length, "h": body_height, "speed": speed, "wiggle": wiggle})
        self.move_fishes()

    def move_fishes(self): 
        # Animates fishes swimming across
        self.fish_tick += 1
        canvas_width = self.bubble_canvas.winfo_width() if self.bubble_canvas.winfo_width() > 0 else 920
        for fish in self.fishes:
            fish['x'] += fish['speed']
            swim = math.sin(self.fish_tick * fish['wiggle']) * 2
            x1, y1 = fish['x'], fish['y'] + swim
            x2, y2 = x1 + fish['w'], y1 + fish['h']
            try:
                if self.bubble_canvas.winfo_exists():
                    self.bubble_canvas.coords(fish['body'], x1, y1, x2, y2)
                    self.bubble_canvas.coords(fish['tail'], x1, (y1+y2)/2, x1 - 10, y1, x1 - 10, y2)
                    if x1 > canvas_width: fish['x'] = -fish['w']
            except tk.TclError: 
                pass 
        if self.fishes and hasattr(self.master, 'winfo_exists') and self.master.winfo_exists():
            self.master.after(40, self.move_fishes)


    def create_debug_window(self):
       # Creates (or shows) the debug log window
        if self.debug_window is not None and self.debug_window.winfo_exists():
            self.debug_window.deiconify() 
            return

        self.debug_window = tk.Toplevel(self.master)
        self.debug_window.title("🪼 Deep Debug Window")
        self.debug_window.geometry("600x400")
        self.debug_window.protocol("WM_DELETE_WINDOW", self.hide_debug_window)

        scroll = tk.Scrollbar(self.debug_window)
        scroll.pack(side=tk.RIGHT, fill=tk.Y)

        self.debug_text = tk.Text(self.debug_window, height=15, bg="#d0f0ff", fg="#003344",
                                font=("Courier New", 9), yscrollcommand=scroll.set, wrap="word",
                                relief=tk.SUNKEN, bd=2)
        self.debug_text.pack(fill="both", expand=True)
        scroll.config(command=self.debug_text.yview)

    # ------------------------------------------------------------------
    def _on_enter_pressed(self, event):
        """Intercept <Return> – send message & eat the newline."""
        self._chat_send_pressed()
        return "break"                 



    def _peer_label(self):
        """Username if we know it, otherwise the 5-digit ID."""
        return self.peer_username_for_session or self.peer_id_for_session or "peer"

    def open_chat_window(self):
        if not self.secure_session_active:
            self.log_msg("⚠️ Secure session not active – chat disabled.")
            return
        if getattr(self, "chat_win", None) and self.chat_win.winfo_exists():
            self.chat_win.deiconify(); self.chat_win.lift(); return

        self.chat_win = tk.Toplevel(self.master)
        self.chat_win.title(f"💬 Chat with {self._peer_label()}")
        self.chat_win.geometry("520x380")
        self.chat_win.protocol("WM_DELETE_WINDOW", self.chat_win.withdraw)

        # history
        hist = tk.Frame(self.chat_win); hist.pack(fill="both", expand=True, padx=5, pady=(5,0))
        scr  = tk.Scrollbar(hist); scr.pack(side=tk.RIGHT, fill=tk.Y)
        self.chat_text = tk.Text(hist, wrap="word", bg="#f7fff9", fg="#123",
                                font=("Segoe UI", 10), state="disabled",
                                yscrollcommand=scr.set)
        self.chat_text.pack(fill="both", expand=True); scr.config(command=self.chat_text.yview)

        # entry
        bar = tk.Frame(self.chat_win); bar.pack(fill="x", padx=5, pady=5)
        self.chat_entry = tk.Text(bar, height=3, font=("Segoe UI", 10))
        self.chat_entry.pack(side=tk.LEFT, fill="x", expand=True, ipady=3); self.chat_entry.focus()
        ttk.Button(bar, text="Send", command=self._chat_send_pressed).pack(side=tk.LEFT, padx=(6,0))
        self.chat_entry.bind("<Return>", self._on_enter_pressed)

    def chat_log(self, who: str, msg: str):
        if not getattr(self, "chat_win", None) or not self.chat_win.winfo_exists():
            self.open_chat_window()
        self.chat_text.config(state="normal")
        self.chat_text.insert(tk.END, f"{who}: {msg}\n")
        self.chat_text.see(tk.END)
        self.chat_text.config(state="disabled")
        # ------------------------------------------------------------------
    def _chat_send_pressed(self) -> None:
        """
        Pull text from the entry widget, transmit through the secure
        channel, then clear the entry.
        """
        msg = self.chat_entry.get("1.0", "end-1c").strip()   # whole text minus trailing NL
        if not msg:
            return

        self.chat_entry.delete("1.0", tk.END)                # clear box
        self.send_secure_message(msg)                        # existing routine



            
    def hide_debug_window(self):
        # Hides the debug log window
        if self.debug_window:
            self.debug_window.withdraw() 

    def prompt_peer_listener_port(self):
        port = simpledialog.askinteger("Initial Peer Comms Channel", "📡 Initial sonar frequency (port) for this sub:", initialvalue=random.randint(10001, 10010))
        if port: 
            self.peer_port = port; self.peer_port_label.config(text=f"📡 Listening on sonar channel {self.peer_port}")
            self._start_peer_listener()
            
        else: self.peer_port_label.config(text="⚠️ Sonar offline!"); self.log_msg("⚠️ Initial sonar port not set.")

    def change_peer_listener_port(self):
        """
        Let the user pick a new local listening port – but ONLY when no
        secure-session is active.
        """
        if self.secure_session_active:
            self.log_msg("⚠️ Cannot change sonar while a secure session is active. "
                        "End it first with ❌ End Session.")
            return

        self.log_msg("⚙️ Adjusting sonar frequency…")
        new_port = simpledialog.askinteger(
            "Change Sonar Channel",
            f"📡 Current channel: {self.peer_port if self.peer_port else 'None'}\n"
            "Enter new sonar frequency (port):",
            initialvalue=self.peer_port if self.peer_port else random.randint(10001, 10010)
        )
        if new_port is None:
            self.log_msg("🚫 Sonar frequency change cancelled.")
            return
        if new_port == self.peer_port and self.peer_listener_thread_ref \
        and self.peer_listener_thread_ref.is_alive():
            self.log_msg(f"📡 Sonar already active on channel {new_port}.")
            return

        self.peer_port = new_port
        self.peer_port_label.config(text=f"📡 Listening on sonar channel {self.peer_port}")
        self._start_peer_listener()


    def clear_animations(self): 
        # Stops and removes all animations
        if hasattr(self, 'bubbles'):
            for bubble_item in self.bubbles:
                try:
                    if self.bubble_canvas.winfo_exists(): self.bubble_canvas.delete(bubble_item['id'])
                except: pass
            self.bubbles.clear()
        if hasattr(self, 'fishes'):
            for fish_item in self.fishes:
                try:
                    if self.bubble_canvas.winfo_exists():
                        self.bubble_canvas.delete(fish_item['body']); self.bubble_canvas.delete(fish_item['tail'])
                except: pass
            self.fishes.clear()

        
    def on_close(self):
        # Handles window close event
        self.log_msg("⚓ Dropping anchor and closing the hatch...")
        self.disconnect_from_server(full_reset=False) # Don't do full reset on close, just socket
        if self.debug_window and self.debug_window.winfo_exists():
            self.debug_window.destroy() 
        self.master.destroy()


 
     #----------------------------------------------------------------------------------
                #CLIENT STATE MANAGEMENT
    #-----------------------------------------------------------------------

    def _reset_p2p_session_state(self):
        """
        Scrub everything related to the current peer-to-peer session, but keep
        long-term credentials (KM/IV).
        """
        self.log_debug("   🐚 Scrubbing the deck! Resetting P2P session details.")
        self.N1 = None
        self.KI = None
        self.N2_local = None
        self.peer_id_for_session = None
        self.peer_target_port_for_session = None
        self.c2_from_server = None
        self.sid_from_server = None
        self.peer_username_for_session = None

        self._is_ecdh_initiator = False
        self._awaiting_n2 = False
        self._awaiting_n2_plus1 = False
        self._awaiting_ecdh_ack = False
        self._awaiting_peer_ecdh_pubkey = False

        # ECDH/session crypto
        self.ec_priv_key = None
        self.ec_pub_key = None
        self.peer_ec_pub_key_bytes = None
        self.KS = None
        self.EKAB = self.EKBA = None
        self.IKAB = self.IKBA = None
        self.IVAB = self.IVBA = None
        self.secure_session_active = False

        self.send_secure_btn.state(['disabled'])


        # ensure UI reflects the idle state
        self._update_session_ui()
        
    def end_session(self):
                """
                Clears all session-related state and keys to safely terminate the current P2P session.
                """
                self.log_msg("❌ Ending current secure session and clearing all related state...")
                self._reset_p2p_session_state()
                self.log_msg("🧼 Secure session state cleared. Ready for a new session.")

                # Reset keys and session flags
                self.KS = None
                self.EKAB = self.EKBA = None
                self.IKAB = self.IKBA = None
                self.IVAB = self.IVBA = None
                self.peer_ec_pub_key_bytes = None
                self.peer_target_port_for_session = None

                self.secure_session_active = False
                self._awaiting_n2 = False
                self._awaiting_n2_plus1 = False
                self._awaiting_peer_ecdh_pubkey = False
                self._awaiting_ecdh_ack = False
                self._is_ecdh_initiator = False


                self.log_msg("🔒 Secure session state cleared. Ready for a new session.")

    
     #----------------------------------------------------------------------------------
            #SERVER COMMUNICATION (CORE)
    #---------------------------------------------------------------------------------------


    def load_keys(self):
         # Loads server's RSA public keys from .pem files
        enc_key_path = filedialog.askopenfilename(title="Select Server Encryption Public Key (.pem)")
        if not enc_key_path: return
        sign_key_path = filedialog.askopenfilename(title="Select Server Signature Public Key (.pem)")
        if not sign_key_path: return

        try:
            self.enc_pub_key = load_rsa_public_key(enc_key_path)
            self.sign_pub_key = load_rsa_public_key(sign_key_path)
            if self.enc_pub_key.export_key() == self.sign_pub_key.export_key(): # Basic check
                self.log_msg("⚠️ Warning: Encryption and signature keys appear to be the same!")
            self.log_msg("✅ Server RSA public keys loaded successfully.")
            self.log_debug(f"🔑 Loaded enc_pub_key (first 100 chars): {self.enc_pub_key.export_key().decode()[:100]}...")
            self.log_debug(f"🔑 Loaded sign_pub_key (first 100 chars): {self.sign_pub_key.export_key().decode()[:100]}...")
            
        except Exception as e:
            messagebox.showerror("Key Load Error", f"Failed to load keys: {e}")
            self.log_msg(f"❌ Error loading RSA keys: {e}")
            self.enc_pub_key = None
            self.sign_pub_key = None

    def connect_to_server(self):
        # Connects to the main authentication server
        if not self.enc_pub_key or not self.sign_pub_key:
            self.log_msg("❌ Hold your seahorses! Unfurl the server's charts (load keys) first.")
            messagebox.showwarning("Keys Required", "Server RSA public keys must be loaded before connecting.")
            return
        if self.conn:
            self.log_msg("🌊 Already navigating the server seas, Captain!")
            return

        self.log_msg("🚢 Preparing to dive... Enter server coordinates.")
        host = simpledialog.askstring("Server Coordinates", "🌐 Enter server's charted IP address:", initialvalue="harpoon1.sabanciuniv.edu")
        if not host:self.log_msg("🚫 Dive cancelled."); return; return
        port = simpledialog.askinteger("Server Coordinates", "⚓ Enter server's docking port:", initialvalue=9999)
        if not port:self.log_msg("🚫 Dive cancelled."); return; return

        try:
            self.conn = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.conn.connect((host, port))
            self.log_msg(f"🟢 Connected to server {host}:{port}")
            
            # Update status based on whether we have KM/IV (implies "logged in")
            if self.auth_success and self.username:
                 self.status_var.set(f"🟢 Connected & Logged in as {self.username}")
                 
            else:
                self.status_var.set(f"🟢 Connected to {host}:{port}. Please authenticate/enroll.")
            self.animate_bubbles() 
        except Exception as e:
            self.conn = None
            messagebox.showerror("Connection Error", str(e))
            self.conn = None; self.log_msg(f"❌ Mayday! Mayday! Connection to server failed: {e}")
            self.status_var.set("🔴 Lost at sea (Disconnected)")

    def disconnect_from_server(self, full_reset=True):
       # Disconnects from server and optionally resets client state
        if self.conn:
            try:
                self.conn.shutdown(socket.SHUT_RDWR)
            except OSError: 
                pass
            finally:
                self.conn.close()
            self.conn = None
            

            self.log_msg("⚓ Submarine surfaced. Disconnected from server currents.")
            if not self.auth_success : # if not truly authenticated (e.g. no KM/IV)
                self.status_var.set("🔴 Disconnected")
            elif self.username:
                 self.status_var.set(f"Logged in as Captain {self.username}. Server currents temporarily lost.")


        if full_reset:
            self.KM = None; self.IV = None
            self.student_id = None; self.username = None 
            self.auth_success = False # Full reset means no longer authenticated
            self.enrollment_status.config(text="")
            self.status_var.set("🔴 Disconnected & Reset")
            
            self.log_msg("🚢 All systems reset. Ready for a new voyage or to load a saved map.")

        # Clear session-specific KI stuff on any disconnect
        self.N1 = None; self.KI = None
        self.c2_from_server = None; self.sid_from_server = None
        self.peer_id_for_session = None; self.N2_local = None
        self.peer_target_port_for_session = None
        self.clear_animations()

    def _recv_exact(self, sock: socket.socket, n: int) -> bytes | None:
        # Helper to receive exactly n bytes from a socket
        if not sock: return None
        buf = b''
        try:
            sock.settimeout(10.0) 
            while len(buf) < n:
                chunk = sock.recv(n - len(buf))
                if not chunk:
                    self.log_msg("❌ Connection closed by remote host while reading.")
                    if sock == self.conn: # Only disconnect if it's the main server connection
                        self.disconnect_from_server(False)
                  
                    return None 
                buf += chunk
            return buf
        except socket.timeout:
            self.log_msg(f"❌ Socket timeout while expecting {n} bytes.")
            return None
        except ConnectionError as e: # This might be raised by sock.recv if connection drops hard
            self.log_msg(f"❌ Connection error during _recv_exact: {e}")
            if sock == self.conn: 
                 self.disconnect_from_server(False)
            return None
        except Exception as e:
            self.log_msg(f"❌ Unexpected error in _recv_exact: {e}")
            if sock == self.conn: 
                 self.disconnect_from_server(False)
            return None
        finally:
            if sock: 
                try: sock.settimeout(None)
                except: pass # Socket might already be closed


    def read_signed_message(self) -> tuple[bytes | None, bytes | None]:
        # Reads a server message: <signature><message_content>
        if not self.conn or not self.sign_pub_key:
            self.log_msg("❌ Cannot read signed message: No connection or signature key.")
            return None, None
        
        sig_len = self.sign_pub_key.size_in_bytes() 
        
        signature = self._recv_exact(self.conn, sig_len) 
        if signature is None:
            self.log_msg("❌ Failed to read signature from server.")
            return None, None

        message_parts = []
        try:
            self.conn.settimeout(0.5) 
            while True:
                chunk = self.conn.recv(4096)
                if not chunk:
                    break 
                message_parts.append(chunk)
        except socket.timeout:
            pass 
        except Exception as e:
            self.log_msg(f"❌ Error reading message part after signature: {e}")
            # Return what was read so far, even if incomplete, along with signature
            return signature, b"".join(message_parts) if message_parts else b'' 
        finally:
            if self.conn: 
                try: self.conn.settimeout(None)
                except: pass
        
        message = b"".join(message_parts)
        if not message:
             self.log_debug("⚠️ Read signature but message part is empty.")
        return signature, message
    


 #----------------------------------------------------------------------------------
             # ENROLLEMENT AND AUTHENTICATION (SERVER INTERACTION - STEP1)
#---------------------------------------------------------------------------------------

    def start_auth_flow(self): # Initiates the authentication/enrollment process with the server

        if not self.conn:
            self.log_msg("⚠️ Dive in first! Connect to the server before identifying the crew.")
            return
        
        # If already "logged in" with saved credentials, confirm re-enrollment
        if self.auth_success and self.username:
            if not messagebox.askyesno("New Voyage?", f"Captain '{self.username}' is already on deck.\nChart a new voyage (re-enroll)? This will require new ship papers (KM/IV).", icon='warning'):
                return
            # Clear existing KM/IV to force new ones if user proceeds
            self.KM = None
            self.IV = None
            self.auth_success = False 
            self.log_msg("Cleared existing KM/IV for re-enrollment.")


        try:
            self.conn.sendall(b"auth")
            self.log_msg("🐙 Requesting passage from the Server Kraken (starting auth)...")
            self.animate_fishes(); self.animate_bubbles() 

            sig, msg = self.read_signed_message()
            if sig is None or msg is None: 
                return

            self.log_debug(f"Auth flow: Received sig_len={len(sig)}, msg_len={len(msg)}")
            self.log_debug(f"Auth flow: Raw message: {msg!r}")
            self.log_debug(f"Auth flow: Decoded message: {msg.decode(errors='replace')}")
            self.log_debug(f"Auth flow: Signature (hex): {sig.hex()}")

            if verify_signature(msg, sig, self.sign_pub_key):
               
                self.log_msg("🛡️ Kraken's scroll is authentic! Proceed to state your crew's name and ship ID.");
                self.send_id_and_username_for_enroll() # New helper for this part
            else:
                
                self.log_msg("❌ The Kraken's scroll is forged! (Invalid server signature for 'auth'). Voyage cancelled.")
        except ConnectionError as ce:
            self.log_msg(f"🚨 Auth flow connection error: {ce}")
            self.disconnect_from_server(full_reset=False)
        except Exception as e:
            self.log_msg(f"🚨 Lost signal with the Kraken! Auth flow error: {e}")

    def send_id_and_username_for_enroll(self):
        # Sends student ID and username to the server as part of enrollment
        student_id_str = simpledialog.askstring("Ship ID", "🆔 Enter your 5-digit Ship ID (Student ID):")
        if not student_id_str or len(student_id_str) != 5:
            self.log_msg("❌ Student ID must be 5 digits.")
            return

        username_str = simpledialog.askstring("Captain's Name", "👤 Choose a unique Captain's Name (Username):")
        if not username_str:
            self.log_msg("❌ Every captain needs a name!")
            return

        # Temporarily store for this enrollment attempt
        current_enroll_student_id = student_id_str
        current_enroll_username    = username_str

        combined = f"{current_enroll_student_id}{current_enroll_username}".encode('utf-8')

        try:
            # Send the concatenated [ID||Username] to the server
            self.conn.sendall(combined)
            self.log_msg(f"📤 Announced Ship ID '{student_id_str}' & Captain '{username_str}'.")

            # Read the server's signed response
            signature, message = self.read_signed_message()
            if signature is None or message is None:
                return

            # Debug output
            self.log_debug(f"Enrollment response: {message.decode(errors='replace')}")
            self.log_debug(f"Enrollment signature: {signature.hex()}")

            # Verify the server's signature
            if verify_signature(message, signature, self.sign_pub_key):
                resp_text = message.decode(errors='replace')
                if "success" in resp_text.lower():
                    self.log_msg("✅ Kraken acknowledges! Awaiting carrier pigeon with secret code (email).")
                    # Proceed to the email code step
                    self.prompt_email_code(current_enroll_student_id, current_enroll_username)
                else:
                    # Use the decoded response_text instead of the undefined msg
                    self.log_msg(f"❌ Kraken denies passage! Enrollment failed: {resp_text}")
            else:
                self.log_msg("❌ Invalid server signature for enrollment response.")
        except ConnectionError as ce:
            self.log_msg(f"🚨 Enrollment connection error: {ce}")
            self.disconnect_from_server(full_reset=False)
        except Exception as e:
            self.log_msg(f"🚨 Error during enrollment: {e}")

    def prompt_email_code(self, enroll_student_id, enroll_username):
        # Handles the email code verification step of enrollment
        if not self.conn:
            self.log_msg("⚠️ Cannot proceed with email code: not connected.")
            return

        code_str = simpledialog.askstring("Email Code", "🐠 Enter the 6-digit code from your email:")
        if not code_str:
            self.log_msg("❌ Email code not entered.")
            return
        code_bytes = code_str.encode('utf-8')

        try:
            self.conn.sendall(b"code")
            self.log_msg("📤 Sent: 'code' command to server.")

            signature, message = self.read_signed_message()
            if signature is None or message is None: return
            self.log_debug(f"Response to 'code' command: {message.decode(errors='replace')}")

            if not verify_signature(message, signature, self.sign_pub_key):
                self.log_msg("❌ Server signature for 'code' response is invalid.")
                return
            if b"success" not in message.lower():
                self.log_msg(f"❌ Server did not successfully acknowledge 'code' command: {message.decode(errors='replace')}")
                return
            
            self.log_msg("✅ Server acknowledged 'code' command. Proceeding with hash and KM||IV.")

            code_hash = hashlib.sha512(code_bytes).digest()
            self.log_debug(f"🔑 SHA512 Hash of code: {code_hash.hex()}")

            secret_32_bytes = get_random_bytes(32)
            # These will become the new self.KM and self.IV if successful
            new_KM = secret_32_bytes[:16] 
            new_IV = secret_32_bytes[16:]
            self.log_debug(f"   ✨ New Treasure Key (KM): {new_KM.hex()}")
            self.log_debug(f"   ✨ New Treasure Map IV (IV): {new_IV.hex()}")
            cipher_rsa = PKCS1_OAEP.new(self.enc_pub_key)
            encrypted_km_iv = cipher_rsa.encrypt(secret_32_bytes)
            self.log_debug(f"   Encrypted Treasure (KM||IV): {encrypted_km_iv.hex()}")

            final_msg_parts = [
                code_hash,
                encrypted_km_iv,
                enroll_student_id.encode('utf-8'), # Use ID from this enrollment attempt
                enroll_username.encode('utf-8')    # Use username from this enrollment attempt
            ]
            final_msg = b"".join(final_msg_parts)
            
            self.conn.sendall(final_msg)
            self.log_debug(f"📦 Final auth msg length: {len(final_msg)} bytes")
            self.log_msg("📤 Sent final authentication message (hash, encrypted KM||IV, ID, username).")

            signature, message = self.read_signed_message()
            if signature is None or message is None: return
            self.log_debug(f"📨 Final auth server response: {message.decode(errors='replace')}")

            if verify_signature(message, signature, self.sign_pub_key) and b"success" in message.lower():
                # Authentication successful, NOW update self. variables and save
                self.KM = new_KM
                self.IV = new_IV
                self.student_id = enroll_student_id
                self.username = enroll_username
                self.auth_success = True # Set to true now
                
                self.log_msg("🎉 Hooray! The Kraken grants passage! Ship papers (KM/IV) secured.")
                self.status_var.set(f"🐠 Authenticated as {self.username}")
                self.enrollment_status.config(text=f"🤝 Captain '{self.username}' (Ship ID: {self.student_id}) officially on the crew list!")
            
                self.save_credentials()
            else:
                self.log_msg("❌ Authentication Failed. Server response indicated failure or invalid signature.")
                # Do not update self.KM, self.IV, self.student_id, self.username
                # self.auth_success remains False or its previous state if already logged in
        except ConnectionError as ce:
            self.log_msg(f"🚨 Email code connection error: {ce}")
            self.disconnect_from_server(full_reset=False)
        except Exception as e:
            self.log_msg(f"🚨 Error during email code verification: {e}")


     #----------------------------------------------------------------------------------
        #ACCOUNT DELETION (SERVER INTERACTION - STEP 1)
    #---------------------------------------------------------------------------------------

    def delete_account(self):
        # Handles account deletion process
        if not self.conn:
            self.log_msg("⚠️ Dive in first ")
            return
        if not self.sign_pub_key: 
            self.log_msg("⚠️ Server signature key not loaded. Cannot verify responses for deletion.")
            return

        self.log_msg("🗑️ Initiating account deletion...")
        try:
            self.conn.sendall(b"delete")
            self.log_msg("📤 Sent: delete")
            sig, msg = self.read_signed_message()
            if not (sig and msg and verify_signature(msg, sig, self.sign_pub_key) and b"success" in msg.lower()):
                self.log_msg(f"❌ Delete init failed: {msg.decode(errors='replace') if msg else 'No/Invalid Response'}")
                return
            
            del_id = simpledialog.askstring("Ship ID to Scuttle", "🆔 Enter Ship ID to scuttle:")
            if not del_id: return
            del_user = simpledialog.askstring("Captain to Scuttle", "👤 Enter Captain's Name to scuttle:")
            if not del_user: return

            self.conn.sendall(f"{del_id}{del_user}".encode())
            self.log_msg(f"📤 Sent {del_id}{del_user} for deletion.")
            sig, msg = self.read_signed_message()
            if not (sig and msg and verify_signature(msg, sig, self.sign_pub_key) and b"success" in msg.lower()):
                self.log_msg(f"❌ Delete ID/User failed: {msg.decode(errors='replace') if msg else 'No/Invalid Response'}")
                return
            self.log_msg("📧 Server should send rcode. Now send 'rcode' command.")

            self.conn.sendall(b"rcode")
            self.log_msg("📤 Sent: rcode")
            sig, msg = self.read_signed_message()
            if not (sig and msg and verify_signature(msg, sig, self.sign_pub_key) and b"success" in msg.lower()):
                self.log_msg(f"❌ 'rcode' command ack failed: {msg.decode(errors='replace') if msg else 'No/Invalid Response'}")
                return
            
            rcode_val = simpledialog.askstring("Removal Code", "🐠 Enter rcode from email:")
            if not rcode_val: return

            self.conn.sendall(f"{rcode_val}{del_id}{del_user}".encode())
            self.log_msg("📤 Sent rcode + ID + Username.")
            sig, msg = self.read_signed_message()
            if sig and msg and verify_signature(msg, sig, self.sign_pub_key) and b"success" in msg.lower():
                self.log_msg("💣 Boom! Account successfully scuttled and sunk to the depths.")
                # If the deleted account was the currently logged-in one, clear credentials
                if self.student_id == del_id and self.username == del_user:
                    self.log_msg(f"✅ Deleted currently logged-in account '{self.username}'. Clearing saved credentials.")
                    if os.path.exists(CREDENTIALS_FILE):
                        try:
                            os.remove(CREDENTIALS_FILE)
                            self.log_debug(f"   Removed {CREDENTIALS_FILE}")
                        except Exception as e_del_file:
                            self.log_debug(f"   Error removing {CREDENTIALS_FILE}: {e_del_file}")
                    self.disconnect_from_server(full_reset=True) # Reset client state

            else:
                self.log_msg(f"❌ Final deletion step failed: {msg.decode(errors='replace') if msg else 'No/Invalid Response'}")

        except ConnectionError as ce:
            self.log_msg(f"🚨 Deletion connection error: {ce}")
            self.disconnect_from_server(full_reset=False)
        except Exception as e:
            self.log_msg(f"⚠️ Deletion error: {e}")


     #----------------------------------------------------------------------------------
            #INTEGRITY KEY (KI) DISTRIBUTION (STEP 2)
    #---------------------------------------------------------------------------------------
    def _drain_server_socket(self) -> None:
        """Read and discard whatever is still pending on the server socket."""
        if not self.conn:
            return
        self.conn.setblocking(False)
        try:
            while self.conn.recv(4096):
                pass                                 # keep reading
        except BlockingIOError:
            pass                                     # nothing left
        finally:
            self.conn.setblocking(True)


     # --- Integrity Key Distribution Methods 
    def request_integrity_key(self):

        if self._awaiting_n2 or self._awaiting_peer_ecdh_pubkey:
            self.log_msg("⏳ Previous KI request still in flight – please wait.")
            return
        """ Client A (initiator) requests KI from the server. (Step 1 & 2 of KI Dist.) """
        if not self.conn:
            self.log_msg("⚠️ Not connected. Cannot request integrity key.")
            return
        
        
        if self.secure_session_active:
            self.log_msg("⚠️ Secure session already active – end it first before requesting a new KI.")
            return

        # Check if KM and IV are loaded/established (self.auth_success should be true)
        if not self.auth_success or not self.KM or not self.IV or not self.student_id or not self.username:
            self.log_msg("⚠️ Client not authenticated (KM/IV missing or not logged in). Please enroll or ensure credentials loaded and connect.")
            return
        self._drain_server_socket()
        self.log_msg("🗺️ Requesting a new treasure map key (KI) from the server...")
        self.KI = None
        self.c2_from_server = self.sid_from_server = None
        self.peer_id_for_session = None

        id_b_str = simpledialog.askstring("Target Diver ID", "🆔 Enter fellow diver's ID (ID_B):")
        if not id_b_str or len(id_b_str.encode()) != ID_LEN: 
            self.log_msg(f"❌ Peer ID must be {ID_LEN} bytes when encoded (e.g., 5 digits).")
            return
        username_b_str = simpledialog.askstring("Target Diver Name", "👤 Enter fellow diver's name (Username_B):")
        self.peer_username_for_session = username_b_str
        if not username_b_str: self.log_msg("❌ Every diver needs a name!"); return

        self.N1 = get_random_bytes(N1_LEN) 

        request_parts = [
            self.student_id.encode('utf-8'), b";",
            self.username.encode('utf-8'), b";",
            id_b_str.encode('utf-8'), b";",
            username_b_str.encode('utf-8'), b";",
            self.N1
        ]
        request_payload = b"".join(request_parts)
        
        try:
            self.conn.sendall(request_payload)
            self.log_msg(f"📤 Message sent to server: Requesting map key for diver {username_b_str} (ID: {id_b_str}).")
            self.log_debug(f"   N1 sent by A: {self.N1.hex()}")

            expected_response_len = C1_CIPHERTEXT_LEN + C2_CIPHERTEXT_LEN + SID_LEN
            raw_response = self._recv_exact(self.conn, expected_response_len)

            if raw_response is None or len(raw_response) < expected_response_len:
                self.log_msg("❌ Server currents are silent... No response for KI request.")
                self._reset_p2p_session_state()
                return

            c1_from_server = raw_response[:C1_CIPHERTEXT_LEN]
            self.c2_from_server = raw_response[C1_CIPHERTEXT_LEN : C1_CIPHERTEXT_LEN + C2_CIPHERTEXT_LEN] 
            self.sid_from_server = raw_response[C1_CIPHERTEXT_LEN + C2_CIPHERTEXT_LEN:]
            self.log_debug(f"   📦 Server's treasure chest received: C1, C2, SID.")

            self.log_debug(f"📦 Received C1 (len {len(c1_from_server)}): {c1_from_server.hex()}")
            self.log_debug(f"📦 Received C2 (len {len(self.c2_from_server)}): {self.c2_from_server.hex()}")
            self.log_debug(f"📦 Received SID (len {len(self.sid_from_server)}): {self.sid_from_server.hex()}")

            self.log_debug(f"   Attempting to decrypt C1 using:")
            self.log_debug(f"     KA (self.KM): {self.KM.hex() if self.KM else 'None'}")
            self.log_debug(f"     IVA (self.IV) for derivation: {self.IV.hex() if self.IV else 'None'}")
            self.log_debug(f"     SID from server for derivation: {self.sid_from_server.hex() if self.sid_from_server else 'None'}")
            
            if not self.KM or not self.IV or not self.sid_from_server: # Should be caught by self.auth_success earlier
                self.log_msg("❌ Critical error: KM, IV, or SID is missing before C1 decryption.")
                return

            iv1_for_c1 = self.derive_iv(self.IV, self.sid_from_server) 
            self.log_debug(f"   🔑 Using own Master Key and derived IV1 ({iv1_for_c1.hex()}) to unlock C1...")

            cipher_aes_a_c1 = AES.new(self.KM, AES.MODE_CBC, iv1_for_c1) 
            P_c1_with_padding = cipher_aes_a_c1.decrypt(c1_from_server) 
            
            self.log_debug(f"🔓 Decrypted C1 (with padding, len {len(P_c1_with_padding)}): {P_c1_with_padding.hex()}")
            
            P_c1_unpadded = b''
            try:
                P_c1_unpadded = unpad(P_c1_with_padding, AES_BLOCK_SIZE, style='pkcs7')
                self.log_debug(f"   Manually unpadded C1 (len {len(P_c1_unpadded)}): {P_c1_unpadded.hex()}")
            except ValueError as ve_unpad: 
                self.log_msg(f"❌ C1 unpadding failed (ValueError): {ve_unpad}.")
                self.log_debug("   This could indicate a key/IV mismatch if padding bytes are not as expected, or corrupted data.")
                self.log_debug(f"   Data before unpad attempt: {P_c1_with_padding.hex()}")
                return
            except Exception as e_unpad: 
                self.log_msg(f"❌ Unexpected error during C1 unpadding: {e_unpad}")
                return
            
            if len(P_c1_unpadded) < KI_LEN + ID_LEN*2 + 1:
                self.log_msg("❌ C1 too short after decrypt/unpad.")
                return

            ki_decrypted  = P_c1_unpadded[:KI_LEN]
            ida_decrypted_bytes = P_c1_unpadded[KI_LEN : KI_LEN+ID_LEN]
            idb_decrypted_bytes = P_c1_unpadded[KI_LEN+ID_LEN : KI_LEN+ID_LEN*2]

            # whatever length is left belongs to N1  (15‥16 bytes in practice)
            n1_decrypted  = P_c1_unpadded[KI_LEN+ID_LEN*2:]

            # Some servers chop leading 0x00 – compare right-aligned
            if n1_decrypted.rjust(N1_LEN, b"\x00") != self.N1:
                self.log_msg("❌ Mismatch in N1. Aborting KI exchange.")
                return

            try:
                ida_decrypted_str = ida_decrypted_bytes.decode('utf-8')
                idb_decrypted_str = idb_decrypted_bytes.decode('utf-8')
            except UnicodeDecodeError:
                self.log_msg("❌ Error decoding IDs from decrypted C1.")
                return

            if ida_decrypted_str != self.student_id:
                self.log_msg(f"❌ Mismatch in IDA (got {ida_decrypted_str}, expected {self.student_id}). Aborting KI exchange.")
                return

            if idb_decrypted_str != id_b_str:                       # <- the missing check
                self.log_msg(f"❌ Mismatch in IDB (got {idb_decrypted_str}, expected {id_b_str}). Aborting KI exchange.")
                return

            if n1_decrypted != self.N1:
                self.log_msg("❌ Mismatch in N1. Aborting KI exchange.")
                return
            
            

            self.log_debug(f"   Parsed from C1: KI={ki_decrypted.hex()}, IDA={ida_decrypted_str}, IDB={idb_decrypted_str}, N1_recv={n1_decrypted.hex()}")

            if ida_decrypted_str != self.student_id or n1_decrypted != self.N1:
                self.log_msg("❌ Mismatch in decrypted IDA or N1 from C1. Protocol aborted.")
                self.log_debug(f"   Expected IDA: {self.student_id}, Got: {ida_decrypted_str}")
                self.log_debug(f"   Expected N1 (A sent): {self.N1.hex()}, Got N1_recv: {n1_decrypted.hex()}")
                return

            self.KI = ki_decrypted
            self.peer_id_for_session = id_b_str 
            self.log_msg(f"✅ KI successfully established with server for peer {id_b_str}!")
            self.log_debug(f"🔑 Stored KI: {self.KI.hex()}")
            self.log_msg("   Next: Client A should send C2 and SID to peer B.")

        except ConnectionError as ce:
            self.log_msg(f"🚨 KI request connection error: {ce}")
        except ValueError as ve: self.log_msg(f"🚨 Stormy seas decrypting C1! (ValueError): {ve}"); self._reset_p2p_session_state()
        except Exception as e: self.log_msg(f"🚨 Kraken attack during KI request! Error: {e}"); self._reset_p2p_session_state(); import traceback; self.log_debug(traceback.format_exc())


    def send_c2_sid_to_peer(self): # Client A sends C2||SID to B
        """ Client A (initiator) sends C2 || SID to Client B (responder). (Step 3 of KI Dist.) """
        if not self.c2_from_server or not self.sid_from_server:
            self.log_msg("⚠️ Cannot send to peer: C2 or SID not available. Complete 'Get KI (A->S)' first.")
            return
        if not self.KI: 
            self.log_msg("⚠️ Cannot send to peer: KI not established. KI flow might have failed.")
            return
        if not self.peer_id_for_session: # This was set in request_integrity_key
            self.log_msg("⚠️ Peer ID for current session not set. Cannot determine target for C2||SID.")
            return

        peer_target_port_str = simpledialog.askstring(
            "Peer Listener Port",
            f"🌊 Enter listening port of peer '{self.peer_id_for_session}':"
        )
        if not peer_target_port_str or not peer_target_port_str.isdigit():
            self.log_msg("❌ Invalid or missing peer port input.")
            return
        try:
            test_port = int(peer_target_port_str)
            if not (1024 <= test_port <= 65535):
                raise ValueError("Out of valid port range")
        except ValueError:
            self.log_msg("❌ Invalid peer port number entered. Resetting session state.")
            self._reset_p2p_session_state()
            return


        payload_to_peer = self.c2_from_server + self.sid_from_server
        self.log_debug(f"📦 Payload to peer (C2||SID, len {len(payload_to_peer)}): {payload_to_peer.hex()}")

        try:
            with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                s.connect(("127.0.0.1", test_port)) 
                s.sendall(self.c2_from_server + self.sid_from_server)
                self.peer_target_port_for_session = test_port  # ← assign only afte successful connect
                self.log_msg(f"🔗 Sent C2||SID to peer {self.peer_id_for_session}.")
                self._awaiting_n2 = True
            self.log_msg(f"📤 Sent C2||SID to peer {self.peer_id_for_session} on 127.0.0.1:{self.peer_target_port_for_session}.")
            self.log_msg("⏳ Client A: Waiting for N2 response from peer B (listener handles this)...")
        except ConnectionRefusedError:
            self.log_msg(f"❌ Peer not listening on {test_port}.  Try another port.")
                # keep the KI / C2 / SID so the user can re-enter the port
            return
        except Exception as e:
            self.log_msg(f"🚨 Error sending C2||SID to peer: {e}")

        
    # ------------------------------------------------------------------
    def _handle_c2_sid_from_peer_bytes(self, buf: bytes):
        """Responder (B) handles C2‖SID sent by initiator (A)."""
        self._is_ecdh_initiator = False          # B is the responder

        total = C2_CIPHERTEXT_LEN + SID_LEN
        if len(buf) != total:
            return self.log_msg(
                f"❌ Client B: expected {total} bytes for C2||SID, got {len(buf)}"
            )

        c2  = buf[:C2_CIPHERTEXT_LEN]
        sid = buf[C2_CIPHERTEXT_LEN:]

        # -- decrypt C2 --------------------------------------------------------
        iv  = self.derive_iv(self.IV, sid)
        try:
            clear = unpad(AES.new(self.KM, AES.MODE_CBC, iv).decrypt(c2),
                        AES_BLOCK_SIZE, style="pkcs7")
        except ValueError as e:
            return self.log_msg(f"❌ Client B: cannot unpad C2: {e}")

        # slice fields
        ki_bytes = clear[:KI_LEN]
        ida_str  = clear[KI_LEN:KI_LEN+ID_LEN].decode("utf-8", "ignore")

        # ----------------------------------------------------------------------
        # first time we see the initiator, remember who we are talking to
        if self.peer_id_for_session is None:
            self.peer_id_for_session = ida_str
        elif ida_str != self.peer_id_for_session:
            return self.log_msg(
                f"❌ Client B: got ID_A={ida_str}, expected {self.peer_id_for_session}"
            )

        # accept KI
        self.KI = ki_bytes
        self.log_msg(f"✅ Client B: established KI with {ida_str}")
        self.log_debug(f"   🔑 KI (hex): {self.KI.hex()}")

        # ----------------------------------------------------------------------
        # move on to step 4 – generate & send N2
        self._awaiting_n2_plus1 = True
        self.master.after(0, self.send_n2_to_initiator)

        
    def send_n2_to_initiator(self):
        """Responder B sends Enc(N2)||IV3 to Initiator A (step 4 of KI)."""
        if not self.KI or not self.peer_id_for_session:
            self.log_msg("⚠️ Client B: Cannot send N2 – KI or peer ID missing.")
            return

        self.N2_local = get_random_bytes(N1_LEN)
        iv3           = get_random_bytes(AES_BLOCK_SIZE)

        cipher   = AES.new(self.KI, AES.MODE_CBC, iv3)
        enc_n2   = cipher.encrypt(pad(self.N2_local, AES_BLOCK_SIZE, 'pkcs7'))
        payload  = enc_n2 + iv3

        # ask only **once** – and then remember it
        if self.peer_target_port_for_session is None:
            port = simpledialog.askinteger("Initiator’s port",
                                        f"Enter listening port of initiator {self.peer_id_for_session}:")
            if port is None:
                return
            self.peer_target_port_for_session = port

        try:
            with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                s.connect(("127.0.0.1", self.peer_target_port_for_session))
                s.sendall(payload)

            self.log_msg(f"📤 Client B: Sent Enc(N2)||IV3 to {self.peer_id_for_session} "
                        f"on port {self.peer_target_port_for_session}.")
            self._awaiting_n2_plus1 = True
            self.log_msg("⏳ Client B: waiting for N2+1 …")
        except Exception as e:
            self.log_msg(f"🚨 Client B: could not send N2: {e}")
            self._reset_p2p_session_state()

    def _handle_enc_n2_from_peer_bytes(self, buf: bytes):# Client A receives Enc(N2)||IV3
        expected = 2*AES_BLOCK_SIZE + AES_BLOCK_SIZE
        if len(buf) != expected:
            return self.log_msg(f"❌ Client A: bad length for Enc(N2)||IV3: {len(buf)}")

        encrypted_n2 = buf[:2*AES_BLOCK_SIZE]
        iv3          = buf[2*AES_BLOCK_SIZE:]

        data = AES.new(self.KI, AES.MODE_CBC, iv3).decrypt(encrypted_n2)
        try:
            n2 = unpad(data, AES_BLOCK_SIZE, style='pkcs7')
        except ValueError as e:
            self.log_msg(f"❌ Client A: invalid padding on N2: {e}")
            return self._reset_p2p_session_state()

        self.N2_local = n2
        self.log_msg("✅ Client A: received and decrypted N2")

        # schedule N2+1→B on the GUI thread
        self.master.after(0, self.send_n2_plus_1_to_responder)

        if buf == expected:
            self.log_msg("🤝 KI handshake complete!  You may now press "
                        "'🚀 Start Secure Session' on either side.")


    def send_n2_plus_1_to_responder(self):
        # Client A sends Enc(N2+1)||IV4
        if not self.KI or not self.N2_local or not self.peer_target_port_for_session: 
            self.log_msg("⚠️ Client A: Cannot send N2+1. KI, received N2, or peer B's port missing.")
            return

        n2_int = int.from_bytes(self.N2_local, 'big')
        n2_plus_1_int = n2_int + 1
        
        try:
            n2_plus_1_bytes = n2_plus_1_int.to_bytes(N1_LEN, 'big') # N2+1 should be same length as N2
        except OverflowError:
            self.log_msg("❌ Client A: Overflow converting N2+1 back to bytes. This is unexpected for a nonce.")
            return

        iv4 = get_random_bytes(AES_BLOCK_SIZE)
        
        padded_N2_plus_1 = pad(n2_plus_1_bytes, AES_BLOCK_SIZE, style='pkcs7')
        cipher_ki_n2p1 = AES.new(self.KI, AES.MODE_CBC, iv4)
        encrypted_n2_plus_1 = cipher_ki_n2p1.encrypt(padded_N2_plus_1) # Should be 32 bytes

        payload_to_B = encrypted_n2_plus_1 + iv4
        self.log_debug(f"   Client A: N2 received from B: {self.N2_local.hex()}")
        self.log_debug(f"   Client A: N2+1 to send to B: {n2_plus_1_bytes.hex()}")
        self.log_debug(f"   Client A: IV4 for N2+1: {iv4.hex()}")
        self.log_debug(f"   Client A: Padded N2+1 for Enc (len {len(padded_N2_plus_1)}): {padded_N2_plus_1.hex()}")
        self.log_debug(f"   Client A: Encrypted N2+1 (len {len(encrypted_n2_plus_1)}): {encrypted_n2_plus_1.hex()}")

        try:
            with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                s.connect(("127.0.0.1", self.peer_target_port_for_session)) 
                s.sendall(payload_to_B)
            self.log_msg(f"📤 Client A: Sent Enc(N2+1)||IV4 to responder B on port {self.peer_target_port_for_session}.")
            self.log_msg(f"✅ Client A: KI exchange presumably complete if B verifies N2+1.")

        except ConnectionRefusedError:
                self.log_msg("❌ Responder not listening on that port.  Try again.")
                # Cancel the “waiting for ACK” stage so user can retry
                self._awaiting_n2_plus1 = False
                # don’t destroy KI – we only abort the KI handshake
                self.N2_local = None
                return
        except Exception as e:
            self.log_msg(f"🚨 Client A: Error sending Enc(N2+1)||IV4 to responder B: {e}")
            self._awaiting_n2_plus1 = False
            self.N2_local = None


    def _handle_enc_n2_plus_1_from_peer_bytes(self, buf: bytes):
         # N2_local for B is the N2 it originally generated and sent to A.
        # peer_id_for_session for B is A's ID.
        expected = 2*AES_BLOCK_SIZE + AES_BLOCK_SIZE
        if len(buf) != expected:
            return self.log_msg(f"❌ Client B: bad length for Enc(N2+1)||IV4: {len(buf)}")

        encrypted_n2p1 = buf[:2*AES_BLOCK_SIZE]
        iv4            = buf[2*AES_BLOCK_SIZE:]

        data = AES.new(self.KI, AES.MODE_CBC, iv4).decrypt(encrypted_n2p1)
        try:
            n2p1 = unpad(data, AES_BLOCK_SIZE, style='pkcs7')
        except ValueError as e:
            self.log_msg(f"❌ Client B: invalid padding on N2+1: {e}")
            return self._reset_p2p_session_state()

        got = int.from_bytes(n2p1, 'big')
        exp = int.from_bytes(self.N2_local, 'big') + 1
        if got == exp:
            self.log_msg("✅ Client B: N2+1 verified—KI handshake complete!")
        else:
            self.log_msg(f"❌ Client B: N2+1 mismatch (got {got}, expected {exp})")


 #----------------------------------------------------------------------------------
                    #SESSION KEY (KS) EXCHANGE (ECDH- STEP 3)
 #---------------------------------------------------------------------------------------


    def start_session_key_exchange(self):
        if not self.KI:
            self.log_msg("⚠️ No integrity key (KI) found. Cannot initiate session.")
            return
        
        if self.KI is None:
            self.log_msg("❌ KI is None. You must get KI from the server before starting the session.")
            return

        from crypto_utils import (
            generate_ecdh_keypair, 
            derive_session_key, 
            hmac_sha256
        )

        # Step 1: Generate own ECC keypair
        self._is_ecdh_initiator = True 
         
        self.ec_priv_key, self.ec_pub_key = generate_ecdh_keypair()
        pub_bytes = self.ec_pub_key.export_key(format='DER')

        # Step 2: Compute HMAC_KI(PUB)
        hmac_pub = hmac_sha256(self.KI, pub_bytes)

        # Step 3: Send pub || HMAC to peer
        combined = pub_bytes + hmac_pub
        self._awaiting_peer_ecdh_pubkey = True

        peer_port = self.peer_target_port_for_session
        if not peer_port:
            peer_port = simpledialog.askinteger("Peer Port", "Enter your peer's port:", initialvalue=self.peer_port)
            if not peer_port:
                return
            


        try:
            with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                s.connect(("127.0.0.1", peer_port))
                s.sendall(combined)
                self.peer_target_port_for_session = peer_port

                self.log_msg("📤 Sent public key + HMAC to peer")

        except ConnectionRefusedError:
            self.log_msg(f"❌ Peer not listening on {peer_port}.  Try again.")
           # roll back *only* the ECDH flags/keys – keep KI so user can retry
            self._awaiting_peer_ecdh_pubkey = False
            self._is_ecdh_initiator         = False
            self.ec_priv_key = self.ec_pub_key = None
            return
        except Exception as e:
            self.log_msg(f"❌ Failed to contact peer: {e}")
            self._awaiting_peer_ecdh_pubkey = False
            self._is_ecdh_initiator         = False
            self.ec_priv_key = self.ec_pub_key = None
            return

        # Step 4: Wait for peer's response in _peer_listener (we will extend it next)
        self.log_debug(f"🔑 My ECC Public Key: {pub_bytes.hex()}")
        self.log_debug(f"🧾 HMAC_KI(PUB): {hmac_pub.hex()}")


    def _handle_peer_connection(self, peer_conn: socket.socket, peer_addr):
        self.log_debug(f"   Decoding signal from {peer_addr}...")
        buf = b'' 
        try:
            peer_conn.settimeout(5.0) 
            while True: 
                chunk = peer_conn.recv(4096)
                if not chunk: break 
                buf += chunk
        except socket.timeout: self.log_debug(f"   Socket timeout receiving from {peer_addr}. Processing {len(buf)} bytes.")
        except Exception as e: self.log_msg(f"🚨 Error receiving full message from {peer_addr}: {e}"); peer_conn.close(); return
        finally: peer_conn.settimeout(None)

        if not buf: self.log_msg(f"⚠️ Empty signal from {peer_addr}."); peer_conn.close(); return
        self.log_debug(f"   Total signal received from {peer_addr}: {len(buf)} bytes.")

        # --- ECDH Key Exchange Handling ---
        # Case 1A: This client is INITIATOR, waiting for peer's PubKey+HMAC
        if self._is_ecdh_initiator and self._awaiting_peer_ecdh_pubkey and len(buf) == ECDH_MSG_LEN and self.KI:
            self.log_debug("   📨 Initiator A: Detected Peer's ECDH Public Key + HMAC...")
            self._awaiting_peer_ecdh_pubkey = False # Consume flag
            
            peer_pub_key_bytes = buf[:-HMAC_SHA256_LEN]
            received_hmac = buf[-HMAC_SHA256_LEN:]
            expected_hmac = hmac_sha256(self.KI, peer_pub_key_bytes)

            if hmac.compare_digest(expected_hmac, received_hmac):
                self.log_msg("✅ Peer's public key integrity verified (HMAC OK).")
                self.peer_ec_pub_key_bytes = peer_pub_key_bytes
                peer_pub_key_obj = ECC.import_key(peer_pub_key_bytes)

                self.KS = derive_session_key(peer_pub_key_obj, self.ec_priv_key)

                self.log_msg(f"🔑 Shared Session Key (KS) derived successfully by Initiator A!")
                self._derive_communication_keys_from_ks() # Helper to derive EKAB etc.
                
                # Initiator A sends ACK
                ack_msg = b"ACK"; ack_hmac = hmac_sha256(self.KI, ack_msg)
                payload_ack_A = ack_msg + ack_hmac
                try:
                    self._awaiting_ecdh_ack = True # Now A waits for B's ACK
                    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                        s.connect(("127.0.0.1", self.peer_target_port_for_session)) # Port of B
                        s.sendall(payload_ack_A)
                    self.log_msg(f"📤 Initiator A: Sent ACK to Responder {self.peer_id_for_session}.")
                    
                except Exception as e: self.log_msg(f"❌ A: Failed to send ACK: {e}"); self._reset_p2p_session_state()
            else:
                self.log_msg("❌ Peer's public key HMAC FAILED! Sending BAD HMAC."); self._send_bad_hmac_to_peer()
            return

        # Case 1B: This client is RESPONDER, receiving Initiator's PubKey+HMAC
        elif not self._is_ecdh_initiator and len(buf) == ECDH_MSG_LEN and self.KI and not self.ec_priv_key:
            self.log_debug("   📨 Responder B: Detected Initiator's ECDH Public Key + HMAC...")
            self.ec_priv_key, self.ec_pub_key = generate_ecdh_keypair() # Responder generates keys now
            self.log_debug(f"      Responder B: ECC Key Pair generated.")

            peer_pub_key_bytes = buf[:-HMAC_SHA256_LEN] # This is A's PubKey
            received_hmac = buf[-HMAC_SHA256_LEN:]
            expected_hmac = hmac_sha256(self.KI, peer_pub_key_bytes)

            if hmac.compare_digest(expected_hmac, received_hmac):
                self.log_msg("✅ Initiator's public key integrity verified (HMAC OK).")
                self.peer_ec_pub_key_bytes = peer_pub_key_bytes
                peer_pub_key_obj = ECC.import_key(peer_pub_key_bytes)

                self.KS = derive_session_key(peer_pub_key_obj, self.ec_priv_key)

                self.log_msg(f"🔑 Shared Session Key (KS) derived successfully by Responder B!")
                self._derive_communication_keys_from_ks()

                # Responder B sends its PubKey+HMAC, then its ACK
                my_pub_key_bytes_B = self.ec_pub_key.export_key(format='DER')
                hmac_my_pub_B = hmac_sha256(self.KI, my_pub_key_bytes_B)
                payload_pub_B = my_pub_key_bytes_B + hmac_my_pub_B

                ack_msg_B = b"ACK"; ack_hmac_B = hmac_sha256(self.KI, ack_msg_B)
                payload_ack_B = ack_msg_B + ack_hmac_B
                
                
                
                def _prompt_and_send():
                    # runs in the Tk-main thread
                    port_A = self.peer_target_port_for_session
                    if port_A is None:
                        port_A = simpledialog.askinteger(
                            "Initiator's Port",
                            f"Enter listening port of ECDH initiator "
                            f"({self.peer_id_for_session}):")
                        if port_A is None:
                            self.log_msg("❌ B: Initiator port not provided. Aborting.")
                            self._reset_p2p_session_state()
                            return
                        self.peer_target_port_for_session = port_A  # remember

                    try:
                        # 1) send my PubKey+HMAC
                        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                            s.connect(("127.0.0.1", port_A))
                            s.sendall(payload_pub_B)
                        self.log_msg(f"📤 Responder B → A: sent PubKey+HMAC")

                        # 2) send ACK
                        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                            s.connect(("127.0.0.1", port_A))
                            s.sendall(payload_ack_B)
                        self.log_msg(f"📤 Responder B → A: sent ACK")
                        self._awaiting_ecdh_ack = True
                    except Exception as e:
                        self.log_msg(f"❌ B: could not send PubKey/ACK: {e}")
                        self._reset_p2p_session_state()

            # schedule the UI prompt & actual sending on the main thread
            self.master.after(0, _prompt_and_send)
            return  # worker thread is done here

        # ── Case 2: receiving ACK / BAD HMAC ─────────────────────────────
        elif (buf.startswith(b"ACK") or buf.startswith(b"BAD HMAC")) \
            and len(buf) <= ACK_MSG_TOTAL_LEN_MAX and self.KI:

            self.log_debug("   📨 Detected ACK/BAD_HMAC from peer…")
            self._awaiting_ecdh_ack = False

            msg_part   = buf[:-HMAC_SHA256_LEN]
            rcvd_hmac  = buf[-HMAC_SHA256_LEN:]
            expected   = hmac_sha256(self.KI, msg_part)

            if hmac.compare_digest(expected, rcvd_hmac):
                if msg_part == b"ACK":
                    self.log_msg("✅ Received ACK from peer. Secure P2P session established!")
                    self.secure_session_active = True
                    self.animate_bubbles()

                    # >>> NEW: open chat window & lock UI
                    self.open_chat_window()
                    self._update_session_ui()
                    # <<<

                    self.log_debug(f"   Secure session active with {self.peer_id_for_session}.")
                else:  # BAD HMAC
                    self.log_msg("❌ Received BAD HMAC from peer. Session key exchange failed.")
                    self._reset_p2p_session_state()
            else:
                self.log_msg("❌ HMAC on ACK/BAD_HMAC from peer is invalid! Session failed.")
                self._reset_p2p_session_state()
            return

        # --- KI Distribution Message Handling ---
        elif self._awaiting_n2: 
            self._awaiting_n2 = False 
            self.log_msg("🐠 Received N2's echo. Deciphering..."); self._handle_enc_n2_from_peer_bytes(buf)
            return
        elif self._awaiting_n2_plus1: 
            self._awaiting_n2_plus1 = False
            self.log_msg("🐡 Received N2+1's ping. Verifying..."); self._handle_enc_n2_plus_1_from_peer_bytes(buf)
            return
        
        # --- END_SESSION control packet -----------------------------------
        elif buf.startswith(b"END_SESSION") and len(buf) == len(b"END_SESSION")+HMAC_SHA256_LEN and self.KI:
            body = buf[:-HMAC_SHA256_LEN]
            mac  = buf[-HMAC_SHA256_LEN:]
            if hmac.compare_digest(mac, hmac_sha256(self.KI, body)):
                self.log_msg("📴 Peer ended the session – cleaning local state.")
                self._reset_p2p_session_state()

                # NEW: close chat window too
                if getattr(self, "chat_win", None) and self.chat_win.winfo_exists():
                    self.chat_win.destroy()

            return
        # ------------------------------------------------------------------

        
        # --- Secure Message Handling ---
        elif self.secure_session_active and self.EKBA and self.IKBA and self.IVBA and len(buf) > HMAC_SHA256_LEN:
            self._handle_secure_message_from_peer(buf)
            return
            
        # Fallback: Assume C2||SID for Responder B if no other state matches
        elif len(buf) == C2_CIPHERTEXT_LEN + SID_LEN:
            if self.N2_local or self.peer_id_for_session or self.KI: 
                self.log_debug("      Clearing old P2P state before becoming Responder (B) for C2||SID.")
                self.KI = None; self.N2_local = None; self.peer_id_for_session = None 
            self.log_msg("🗺️ Received map piece (C2||SID). Acting as Responder (B)...")
            self._handle_c2_sid_from_peer_bytes(buf)
            return
        
        else: 
            self.log_msg("⚠️ Unidentified signal or ambiguous client state.")
            self.log_debug(f"   State: N1:{self.N1 is not None}, KI:{self.KI is not None}, N2_l:{self.N2_local is not None}, PeerID:{self.peer_id_for_session}, ECDH_Init:{self._is_ecdh_initiator}, AwaitPubKey:{self._awaiting_peer_ecdh_pubkey}, AwaitACK:{self._awaiting_ecdh_ack}")
            self.log_debug(f"   Rcvd len: {len(buf)}")





   # ------------------------------------------------------------------
    def _derive_communication_keys_from_ks(self) -> None:
        """
        Expand the 256-bit KS into six 128-bit secrets.

        This routine **only** derives and stores the keys; it does *not*
        touch the UI (chat window / buttons).  UI updates happen after the
        final ACK exchange so that both sides are synchronised first.
        """
        if not self.KS:
            self.log_debug("⚠️ _derive_communication_keys_from_ks: KS missing.")
            return

        raw96 = shake128_expand(self.KS, 96)        # 96-byte stretch

        self.EKAB, self.EKBA = raw96[0:16],  raw96[16:32]
        self.IKAB, self.IKBA = raw96[32:48], raw96[48:64]
        self.IVAB, self.IVBA = raw96[64:80], raw96[80:96]

        self.log_debug(f"   EKAB={self.EKAB.hex()}  EKBA={self.EKBA.hex()}")
        self.log_debug(f"   IKAB={self.IKAB.hex()}  IKBA={self.IKBA.hex()}")
        self.log_debug(f"   IVAB₀={self.IVAB.hex()} IVBA₀={self.IVBA.hex()}")


   
    def _get_outbound_crypto(self):
        """
        Return (EK, IK, IV) to *send* a message   (our → peer).
        Initiator = party A  ⟹  use  _AB  keys
        Responder = party B  ⟹  use  _BA  keys
        """
        if self._is_ecdh_initiator:
            return self.EKAB, self.IKAB, self.IVAB
        else:
            return self.EKBA, self.IKBA, self.IVBA


    def _get_inbound_crypto(self):
        """
        Return (EK, IK, IV) to *receive* a message (peer → us).
        Exactly the opposite direction of _get_outbound_crypto.
        """
        if self._is_ecdh_initiator:
            return self.EKBA, self.IKBA, self.IVBA
        else:
            return self.EKAB, self.IKAB, self.IVAB
   

     #----------------------------------------------------------------------------------
            #SECURE P2P MESSAGING (STEP 3)
    #----------------------------------------------------------------------------------



    def send_secure_message_prompt(self):
        # Prompts user for a message and calls send_secure_message
        if not self.secure_session_active:
            self.log_msg("❌ Secure P2P session not active. Complete session key exchange first.")
            messagebox.showwarning("No Secure Session", "Please establish a secure session with a peer first using 'Start Secure Session'.")
            return
        
        msg_to_send = simpledialog.askstring("Secure Transmission", "Captain, your secret message to your peer:")
        if msg_to_send:
            self.send_secure_message(msg_to_send)
        else:
            self.log_msg("🚫 Secure message transmission cancelled.")

    
    def send_secure_message(self, message_text: str):
        """
        Encrypt `message_text` and send it to the peer over the active
        secure P2P channel.

        The correct (EK, IK, IV) triple depends on whether we are the
        ECDH-initiator (party A) or responder (party B); use
        self._get_outbound_crypto() to obtain it.
        """
        if not self.secure_session_active:
            self.log_msg("❌ Cannot send secure message: secure session not active.")
            return

        # pick the outbound keys for *this* side
        ek, ik, iv = self._get_outbound_crypto()
        if not all([ek, ik, iv, self.peer_target_port_for_session]):
            self.log_msg("❌ Cannot send secure message: session parameters missing.")
            return

        try:
            preview = (message_text[:30] + "…") if len(message_text) > 30 else message_text
            self.log_msg(f"🔒 Preparing to send secure message: '{preview}'")

            cipher     = AES.new(ek, AES.MODE_CBC, iv)
            padded_msg = pad(message_text.encode("utf-8"), AES_BLOCK_SIZE, style="pkcs7")
            ciphertext = cipher.encrypt(padded_msg)

            mac        = hmac_sha256(ik, ciphertext)          # from crypto_utils
            payload    = ciphertext + mac
            self.log_debug(f"   Secure payload → peer: ct={len(ciphertext)}  mac={len(mac)}")

            with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                s.connect(("127.0.0.1", self.peer_target_port_for_session))
                s.sendall(payload)

            self.log_msg(f"📤 Secure message sent to diver {self.peer_id_for_session}!")
            self.chat_log("Me", message_text)

          
            # bump ONLY the IV we have just used (direction-specific)
            if self._is_ecdh_initiator:
                # initiator’s outbound direction is  A → B   ↦  IVAB
                self.IVAB = update_iv(self.IVAB)
                self.log_debug(f"   Updated IV_AB for next A→B message: {self.IVAB.hex()}")
            else:
                # responder’s outbound direction is B → A   ↦  IVBA
                self.IVBA = update_iv(self.IVBA)
                self.log_debug(f"   Updated IV_BA for next B→A message: {self.IVBA.hex()}")
            

        except Exception as e:
            self.log_msg(f"🚨 Error sending secure message: {e}")
            import traceback; self.log_debug(traceback.format_exc())
   
    def send_end_session(self) -> None:
        """
        Notify the peer that we are terminating the secure session and then
        wipe all local session state.
        """
        if not self.secure_session_active or not self.KI:
            self.log_msg("⚠️ No active secure session to terminate.")
            return

        msg = b"END_SESSION"
        tag = hmac_sha256(self.KI, msg)

        try:
            with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                s.connect(("127.0.0.1", self.peer_target_port_for_session))
                s.sendall(msg + tag)
            self.log_msg("📴 Sent END_SESSION signal to peer.")
        except Exception as e:
            self.log_msg(f"❌ Could not send END_SESSION: {e}")

        # Always clear our own state afterwards
        self._reset_p2p_session_state()

        # >>> NEW: update UI & close chat window
        self._update_session_ui()
        if getattr(self, "chat_win", None) and self.chat_win.winfo_exists():
            self.chat_win.destroy()
       

        self.log_msg("🧼 Local session state wiped.")
        self.send_secure_btn.state(['disabled'])


    def _handle_secure_message_from_peer(self, buf: bytes) -> None:
        """
        Process an incoming ciphertext||HMAC frame.

        1.  Pick the correct inbound EK / IK / IV depending on who we are
            (initiator ↔ responder).
        2.  Separate ciphertext (len-32) and tag (32 bytes).
        3.  Verify the HMAC-SHA-256 tag.
        4.  Decrypt and unpad the plaintext.
        5.  Show it in the Voyage log.
        6.  Bump the IV for the *next* inbound message.
        """
        ek, ik, iv = self._get_inbound_crypto()
        if not all([ek, ik, iv]):
            self.log_msg("⚠️ Secure message arrived but inbound keys missing.")
            return

        if len(buf) < 32:
            self.log_msg("⚠️ Secure payload too short – discarded.")
            return

        ciphertext, tag = buf[:-32], buf[-32:]
        expected_tag    = hmac_sha256(ik, ciphertext)

        if not hmac.compare_digest(tag, expected_tag):
            self.log_msg("❌ BAD HMAC on incoming secure message – discarded.")
            return

        try:
            cipher     = AES.new(ek, AES.MODE_CBC, iv)
            padded_pt  = cipher.decrypt(ciphertext)
            plaintext  = unpad(padded_pt, AES_BLOCK_SIZE, style="pkcs7").decode("utf-8", "replace")
        except Exception as e:
            self.log_msg(f"❌ Decryption / unpad error: {e}")
            return

        # Show the message
        self.log_msg(f"💬 Secure message from diver {self.peer_id_for_session}: {plaintext}")
        self.chat_log(self._peer_label(), plaintext)

        # Advance the inbound IV
        if self._is_ecdh_initiator:
            # A ← B direction uses IV_BA
            self.IVBA = update_iv(self.IVBA)
            self.log_debug(f"   Updated IV_BA after inbound msg: {self.IVBA.hex()}")
        else:
            # B ← A direction uses IV_AB
            self.IVAB = update_iv(self.IVAB)
            self.log_debug(f"   Updated IV_AB after inbound msg: {self.IVAB.hex()}")




     #----------------------------------------------------------------------------------
            #PEER LISTENER AND CONNECTION HANDLING
     #----------------------------------------------------------------------------------
    def _start_peer_listener(self):
        if self.peer_port is None: self.log_msg("⚠️ Cannot start sonar: No port."); return
        self._stop_existing_listener()
        self._stop_listener_event.clear()
        self.peer_listener_thread_ref = threading.Thread(target=self._peer_listener_thread, daemon=True)
        self.peer_listener_thread_ref.start()
        # self.peer_port_label.config(text=f"📡 Listening on sonar channel {self.peer_port}") # Already set by prompt/change
        self.log_msg(f"📡 Sonar activated on channel {self.peer_port}.")

    def _peer_listener_thread(self):
        if not self.peer_port: self.log_debug("   Sonar (peer listener) not initialized."); return
        try:
            self.peer_listener_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.peer_listener_socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            self.peer_listener_socket.bind(("127.0.0.1", self.peer_port))
            self.peer_listener_socket.settimeout(1.0); self.peer_listener_socket.listen(5) 
            self.log_debug(f"   📡 Sonar active! Listening for fellow divers on channel {self.peer_port}...")
        except Exception as e: self.log_msg(f"🚨 Sonar malfunction! Cannot listen: {e}"); self.peer_listener_socket = None; return
        try:
            while not self._stop_listener_event.is_set(): 
                try:
                    conn, addr = self.peer_listener_socket.accept() 
                    self.log_msg(f"🌊 Incoming signal from {addr} on our sonar channel!")
                    threading.Thread(target=self._handle_peer_connection, args=(conn,addr), daemon=True).start()
                except socket.timeout: continue 
                except Exception as e_accept: 
                    if self._stop_listener_event.is_set(): break
                    self.log_msg(f"🚨 Sonar interference! Error accepting: {e_accept}"); break 
        finally:
            if self.peer_listener_socket: self.peer_listener_socket.close(); self.peer_listener_socket = None
            self.log_debug(f"   🛑 Sonar on channel {self.peer_port} powered down.")

    def _stop_existing_listener(self):
        if self.peer_listener_thread_ref and self.peer_listener_thread_ref.is_alive():
            self.log_debug("   🛑 Signaling existing sonar listener to stop...")
            self._stop_listener_event.set()
            if self.peer_listener_socket:
                try: # Attempt to wake up the listener
                    temp_sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM); temp_sock.settimeout(0.1)
                    temp_sock.connect(("127.0.0.1", self.peer_port)); temp_sock.close()
                except: pass # Ignore if it fails, thread might be closing
            self.peer_listener_thread_ref.join(timeout=1.5)
            if self.peer_listener_thread_ref.is_alive(): self.log_msg("⚠️ Old sonar listener didn't stop quickly.")
            else: self.log_debug("   ✅ Old sonar listener stopped.")
        self.peer_listener_thread_ref = None; self.peer_listener_socket = None

 #----------------------------------------------------------------------------------
                #CREDENTIAL MANAGEMENT
#------------------------------------------------------------------------------------

    def save_credentials(self):
        """Saves the current student_id, username, KM (hex), and IV (hex) to a file."""
        if not self.student_id or not self.username or not self.KM or not self.IV:
            self.log_debug("⚠️ Attempted to save credentials, but some are missing.")
            return

        credentials = {
            "student_id": self.student_id,
            "username": self.username,
            "km_hex": self.KM.hex(),
            "iv_hex": self.IV.hex()
        }
        try:
            with open(CREDENTIALS_FILE, 'w') as f:
                json.dump(credentials, f, indent=4)
            self.log_msg(f"🔑 Credentials saved for user '{self.username}'.")
            self.log_debug(f"   Saved to {CREDENTIALS_FILE}")
        except IOError as e:
            self.log_msg(f"❌ Error saving credentials: {e}")
            self.log_debug(f"   IOError while saving to {CREDENTIALS_FILE}: {e}")
        except Exception as e:
            self.log_msg(f"❌ Oh barnacles! Could not bury the treasure map (save credentials): {e}")
            self.log_debug(f"   Exception while saving credentials: {e}")

    
    def load_credentials(self):
        """Loads credentials from the file if it exists and updates the client state."""
        if os.path.exists(CREDENTIALS_FILE):
            try:
                with open(CREDENTIALS_FILE, 'r') as f:
                    credentials = json.load(f)
                    
                
                self.student_id = credentials.get("student_id")
                self.username = credentials.get("username")
                km_hex = credentials.get("km_hex")
                iv_hex = credentials.get("iv_hex")

                if self.student_id and self.username and km_hex and iv_hex:
                    self.KM = bytes.fromhex(km_hex)
                    self.IV = bytes.fromhex(iv_hex)
                    self.auth_success = True # KM/IV are present, implying prior auth with server for these keys
                    
                    self.log_msg(f"🗺️ Found a buried treasure map for '{self.username}'! Credentials loaded.")
                    
                    self.log_debug(f"   Loaded Student ID: {self.student_id}")
                    self.log_debug(f"   Loaded Username: {self.username}")
                    self.log_debug(f"   Loaded KM (hex): {self.KM.hex()}")
                    self.log_debug(f"   Loaded IV (hex): {self.IV.hex()}")
                    self.enrollment_status.config(text=f"👤 Logged in as '{self.username}' (ID: {self.student_id})")
                    self.status_var.set(f"🐠 Ahoy, Captain {self.username}! Ready the charts & dive in!")
                    return True
                else:
                    self.log_msg("⚠️ Credentials file found but incomplete. Please enroll again.")
                    self.log_debug("   Credentials file was missing some fields.")
                    os.remove(CREDENTIALS_FILE) 
                   
            except json.JSONDecodeError:
                self.log_msg("❌ Error decoding credentials file. It might be corrupted. Please enroll again.")
                self.log_debug(f"   JSONDecodeError for {CREDENTIALS_FILE}.")
                os.remove(CREDENTIALS_FILE) 
            except Exception as e:
                self.log_msg(f"❌ Shiver me timbers! Error reading the treasure map (credentials): {e}")
                self.log_debug(f"   Exception while loading credentials: {e}")
        else:
            self.log_msg("ℹ️ No treasure map found. Chart a new course (enroll) to begin your voyage!")
            self.log_debug(f"   Credentials file {CREDENTIALS_FILE} not found.")
        return False


#----------------------------------------------------------------------------------  
             #LOGGING AND DEBUGGING UTILITIES
#----------------------------------------------------------------------------------

    def log_msg(self, text):
        
        if hasattr(self, 'msg_text') and self.msg_text and self.msg_text.winfo_exists():
            self.msg_text.insert(tk.END, "🐬 " + text + "\n")
            self.msg_text.see(tk.END)
        if hasattr(self, 'status_var'): self.status_var.set(text[:100])

    def log_debug(self, text):
        
        if hasattr(self, "debug_text") and self.debug_text and self.debug_text.winfo_exists():
            self.debug_text.insert(tk.END, text + "\n")
            self.debug_text.see(tk.END)
        else:
            print(f"DEBUG (Window N/A): {text}") 
    
   

    #----------------------------------------------------------------------------------
                          #CRYPTOGRAPHIC UTILITIES
    #----------------------------------------------------------------------------------

    
   
    def derive_iv(self, static_iv: bytes, sid: bytes) -> bytes:
        # Derives an IV for AES: SHA256(static_IV || SID)[:16]
        if not static_iv or not sid:
            self.log_msg("❌ Cannot derive IV: static_iv or sid is missing.")
            raise ValueError("Static IV and SID must be provided for IV derivation.")
        if len(static_iv) != AES_BLOCK_SIZE or len(sid) != SID_LEN: # SID_LEN should be 16
            self.log_msg(f"❌ Invalid lengths for IV derivation: static_iv ({len(static_iv)}), sid ({len(sid)})")
            raise ValueError("Incorrect length for static_iv or sid in derive_iv.")
            
        h = SHA256.new(static_iv + sid)
        return h.digest()[:AES_BLOCK_SIZE] 
