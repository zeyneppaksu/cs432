import tkinter as tk
from tkinter import messagebox, simpledialog, filedialog, ttk
from crypto_utils import verify_signature,load_rsa_public_key
import socket
import hashlib
from Crypto.Cipher import PKCS1_OAEP
from Crypto.Random import get_random_bytes
from Crypto.Hash import SHA256
import random
import math
from Crypto.Cipher import AES
from Crypto.Cipher import PKCS1_OAEP



def derive_iv(static_iv: bytes, sid: bytes) -> bytes:
    """
    IVᵢ = SHA256(static_iv || SID)[:16]
    """
    h = SHA256.new(static_iv + sid).digest()
    return h[:16]

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
        #main window
        self.master = master
        master.title("🐠 Secure Underwater Client 🐠")
        master.geometry("920x720")
        master.configure(bg="#cceeff")  
        #server public keys
        self.enc_pub_key = None 
        self.sign_pub_key = None


        self.master.protocol("WM_DELETE_WINDOW", self.on_close) #for window closing

        # canvas for bubble/fish animations
        self.bubble_canvas = tk.Canvas(master, height=150, bg="#cceeff", highlightthickness=0)
        self.bubble_canvas.pack(fill="x")
        self.bubbles = []
        self.bubble_tick = 0

        self.fishes = []

        # top frame for control buttons
        self.top_frame = tk.Frame(master, bg="#cceeff", pady=10)
        self.top_frame.pack()

        style = ttk.Style()
        style.theme_use('clam')
        style.configure("TButton",
                        padding=6,
                        relief="flat",
                        background="#3399ff",
                        foreground="white",
                        font=('Helvetica', 10, 'bold'))
        

        # Buttons: load keys, connect, auth, enroll, delete, disconnect “Get KI” 
        self.load_key_btn = ttk.Button(self.top_frame, text="🔑 Load Server Keys", command=self.load_keys)
        self.load_key_btn.grid(row=0, column=0, padx=8)

        self.connect_btn = ttk.Button(self.top_frame, text="🌊 Connect", command=self.connect_to_server)
        self.connect_btn.grid(row=0, column=1, padx=8)

        self.auth_btn = ttk.Button(self.top_frame, text="🐙 Start Auth", command=self.start_auth_flow)
        self.auth_btn.grid(row=0, column=2, padx=8)

        self.enroll_btn = ttk.Button(self.top_frame, text="🐚 Enroll", command=self.send_id_and_username)
        self.enroll_btn.grid(row=0, column=3, padx=8)

        self.delete_btn = ttk.Button(self.top_frame, text="🗑️ Delete Account", command=self.delete_account)
        self.delete_btn.grid(row=0, column=4, padx=8)

        self.disconnect_btn = ttk.Button(self.top_frame, text="🔴 Disconnect", command=self.disconnect_from_server)
        self.disconnect_btn.grid(row=0, column=5, padx=8)

        self.ki_btn = ttk.Button(self.top_frame, text="🔑 Get Integrity Key", command=self.request_integrity_key)
        self.ki_btn.grid(row=0, column=6, padx=8)

       # Message window 
        self.msg_frame = ttk.LabelFrame(master, text="🪸 Coral Message Window", padding=10, style="TLabelframe")
        self.msg_frame.pack(padx=10, pady=5, fill="both", expand=True)

        self.msg_scroll = tk.Scrollbar(self.msg_frame)
        self.msg_scroll.pack(side=tk.RIGHT, fill=tk.Y)

        self.msg_text = tk.Text(self.msg_frame, height=10, bg="#e0f7ff", fg="black",
                                font=("Comic Sans MS", 10), yscrollcommand=self.msg_scroll.set, wrap="word",
                                relief=tk.RIDGE, bd=3)
        self.msg_text.pack(fill="both", expand=True)
        self.msg_scroll.config(command=self.msg_text.yview)

        # Debug window 
        """self.debug_frame = ttk.LabelFrame(master, text="🪼 Deep Debug Window", padding=10, style="TLabelframe")
        self.debug_frame.pack(padx=10, pady=5, fill="both", expand=True)

        self.debug_scroll = tk.Scrollbar(self.debug_frame)
        self.debug_scroll.pack(side=tk.RIGHT, fill=tk.Y)

        self.debug_text = tk.Text(self.debug_frame, height=15, bg="#d0f0ff", fg="#003344",
                                  font=("Courier New", 9), yscrollcommand=self.debug_scroll.set, wrap="word",
                                  relief=tk.SUNKEN, bd=2)
        self.debug_text.pack(fill="both", expand=True)
        self.debug_scroll.config(command=self.debug_text.yview)"""
        # seperate Debug window 

        self.debug_window = tk.Toplevel(self.master)
        self.debug_window.title("🪼 Deep Debug Window")
        self.debug_scroll = tk.Scrollbar(self.debug_window)
        self.debug_scroll.pack(side=tk.RIGHT, fill=tk.Y)

        self.debug_text = tk.Text(self.debug_window, height=15, bg="#d0f0ff", fg="#003344",
                                  font=("Comic Sans MS", 10), yscrollcommand=self.debug_scroll.set, wrap="word",
                                  relief=tk.SUNKEN, bd=2)
        self.debug_text.pack(fill="both", expand=True)
        self.debug_scroll.config(command=self.debug_text.yview)
          # Status bar at bottom
        self.status_var = tk.StringVar()
        self.status_var.set("🔴 Submarine Disconnected")
        self.status_bar = tk.Label(master, textvariable=self.status_var, relief=tk.SUNKEN,
                                   anchor=tk.W, bg="#99ccff", fg="black", font=("Segoe UI", 10, 'italic'))
        self.status_bar.pack(fill="x", side="bottom")

        self.conn = None #track current connection
        self.auth_success = False  #must auth before trying to enroll


    """ animate fishes and bubbles are just for fun in UI so the following functions has nothing to do with the term project 
    whoever checking the code can jump the following 4 functions"""
    def animate_bubbles(self):
        self.bubbles.clear()
        for _ in range(30):
            x = random.randint(30, 880)
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
        self.bubble_tick += 1
        for bubble in self.bubbles[:]:
            bubble['y'] -= bubble['speed']
            wobble = math.sin(self.bubble_tick * bubble['wiggle']) * 2
            x1 = bubble['x'] + wobble
            y1 = bubble['y']
            x2 = x1 + bubble['size']
            y2 = y1 + bubble['size']

            self.bubble_canvas.coords(bubble['id'], x1, y1, x2, y2)

            if y2 <= 0:
                self.bubble_canvas.delete(bubble['id'])
                self.bubbles.remove(bubble)

        if self.bubbles:
            self.master.after(30, self.move_bubbles)
            
    
    def animate_fishes(self):
        self.fishes = []
        self.fish_tick = 0

        for _ in range(8):
            x = random.randint(0, 850)
            y = random.randint(30, 130)
            body_length = random.randint(30, 50)
            body_height = body_length // 2
            speed = random.uniform(1.0, 2.0)
            wiggle = random.uniform(0.05, 0.2)
            color = random.choice(["#ffa07a", "#ff6347", "#ff8c00", "#f08080"])

            body = self.bubble_canvas.create_oval(x, y, x + body_length, y + body_height, fill=color, outline="")

            tail = self.bubble_canvas.create_polygon(
                x, y + body_height // 2,              
                x - 10, y,                           
                x - 10, y + body_height,              
                fill=color, outline=""
            )

            self.fishes.append({
                "body": body,
                "tail": tail,
                "x": x,
                "y": y,
                "w": body_length,
                "h": body_height,
                "speed": speed,
                "wiggle": wiggle
            })

        self.move_fishes()

    def move_fishes(self):
        self.fish_tick += 1
        for fish in self.fishes:
            fish['x'] += fish['speed']
            swim = math.sin(self.fish_tick * fish['wiggle']) * 2
            x1 = fish['x']
            y1 = fish['y'] + swim
            x2 = x1 + fish['w']
            y2 = y1 + fish['h']

            self.bubble_canvas.coords(fish['body'], x1, y1, x2, y2)

            tail_tip_x = x1
            tail_top = y1
            tail_bottom = y2
            tail_center_y = (tail_top + tail_bottom) / 2

            self.bubble_canvas.coords(fish['tail'],
                tail_tip_x, tail_center_y,
                tail_tip_x - 10, tail_top,
                tail_tip_x - 10, tail_bottom
            )

            if x1 > 920:
                fish['x'] = -fish['w']

        self.master.after(40, self.move_fishes)

    def load_keys(self):
        """asks user to pick .pem files and load RSA public keys"""
        enc_key_path = filedialog.askopenfilename(title="Select Server Encryption Public Key (.pem)")
        sign_key_path = filedialog.askopenfilename(title="Select Server Signature Public Key (.pem)")

        self.enc_pub_key = load_rsa_public_key(enc_key_path)
        self.sign_pub_key = load_rsa_public_key(sign_key_path)
        if self.enc_pub_key.export_key() == self.sign_pub_key.export_key():
            self.log_msg("⚠️ Warning: Encryption and signature keys appear to be the same!")


        self.log_msg("✅ Encryption key and signature key loaded succesfuly.")
        self.log_debug(f"🔑 enc_pub_key: {self.enc_pub_key.export_key().decode()[:100]}...")
        self.log_debug(f"🔑 sign_pub_key: {self.sign_pub_key.export_key().decode()[:100]}...")


    def log_msg(self, text):
        self.msg_text.insert(tk.END, "🐬 " + text + "\n")
        self.msg_text.see(tk.END)
        self.status_var.set(text)

    def log_debug(self, text):
        self.debug_text.insert(tk.END, text + "\n")
        self.debug_text.see(tk.END)

    def connect_to_server(self):
        """Open TCP socket to server."""
        # prevent the connection if keys are not loaded
        if not self.enc_pub_key or not self.sign_pub_key:

            self.log_msg("❌ Please load both encryption and signature public keys before connecting.")
            messagebox.showwarning("Keys Required", "You must load the RSA public keys before connecting to the server.")
            self.log_debug("🔐 Connect blocked: RSA keys not loaded.")
            return


        # prevents the duplicate connection attempts
        if self.conn:
            self.log_msg("⚠️ Already connected to a server.")
            return

        host = simpledialog.askstring("Input", "🌐 Enter server IP:", initialvalue="harpoon1.sabanciuniv.edu")
        port = simpledialog.askinteger("Input", "📱 Enter port:", initialvalue=9999)

        try:
            self.conn = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.conn.connect((host, port))
            self.log_msg(f"🟢 Submarine linked to {host}:{port}")
            self.animate_bubbles()
        
        except Exception as e:
            self.conn = None
            messagebox.showerror("Connection Error", str(e))
            self.log_msg("🔴 Connection to coral reef failed.")


    def start_auth_flow(self):
        """send 'auth', read signed welcome, and verify."""
        if not self.conn:
            self.log_msg("⚠️ Dive in first (connect).")
            return

        try:
            # send the auth request
            self.conn.sendall(b"auth")
            self.log_msg("📤 Sent: auth")
            self.animate_fishes(); self.animate_bubbles()

            # read exactly 256 bytes of signature + the full message
            sig, msg = self.read_signed_message()


            # debug
            self.log_debug(f"🔢 Received sig_len={len(sig)}, msg_len={len(msg)}")
            self.log_debug(f"📥 Raw message: {msg!r}")
            self.log_debug(f"📝 Decoded: {msg.decode('utf-8','replace')}")
            self.log_debug(f"🔍 SHA256: {SHA256.new(msg).hexdigest()}")
            self.log_debug(f"🧾 Signature: {sig.hex()}")

            # verify
            if verify_signature(msg, sig, self.sign_pub_key):
                self.auth_success = True
                self.log_msg("🛡️ Server signature verified. Anchors secure!")
            else:
                self.auth_success = False
                self.log_msg("❌ Invalid signature! The fish are suspicious.")

        except ConnectionError as ce:
            # socket closed 
            self.log_msg(f"🚨 Auth flow aborted: {ce}")
            self.disconnect_from_server()
        except Exception as e:
            # catch any other error 
            self.log_msg(f"🚨 Auth torpedo error: {e}")


    def send_id_and_username(self):
        """performs enrollment, sends student ID + username."""
        if not self.conn:
            self.log_msg("⚠️ Dive in first (connect).")
            return

        # enforce auth-first 
        if not getattr(self, "auth_success", False):
            self.log_msg("⚠️ You must start authentication before enrolling.")
            return

        self.student_id = simpledialog.askstring("Student ID", "🐟 Enter your 5-digit diver ID:")
        self.username = simpledialog.askstring("Username", "🐚 Choose a unique shell name:")
        
        combined = f"{self.student_id}{self.username}".encode()

        try:
            self.conn.sendall(combined)
            self.log_msg(f"📤 Sent Diver ID + Shell Name: {combined.decode()}")

            signature, message = self.read_signed_message()


            self.log_debug(f"📩 Response from reef: {message.decode()}")
            self.log_debug(f"🧾 Signature: {signature.hex()}")
            self.animate_bubbles()

            if verify_signature(message, signature, self.sign_pub_key):
                if b"success" in message.lower():
                    self.log_msg("✅ Enrollment to the reef successful!")
                    self.prompt_email_code()
                else:
                    self.log_msg("❌ Enrollment Failed. Fish said no.")
            else:
                self.log_msg("❌ Signature invalid. Shark warning!")

        except Exception as e:
            self.log_msg(f"🚨 Enrollment problem: {e}")

    def prompt_email_code(self):
        """continue the authentication by sending the 6-digit code."""
        code = simpledialog.askstring("Email Code", "🐠 Enter your 6-digit coral code:")
        code_bytes = code.encode()

        try:
            #  tell server we’re sending the code
            self.conn.sendall(b"code")
            self.log_msg("📤 Sent: code")

            #  read signed “start code verification” response
            signature, message = self.read_signed_message()
            self.log_debug(f"📩 Coral Response: {message.decode()}")

            if not verify_signature(message, signature, self.sign_pub_key):
                self.log_msg("❌ Coral verification failed.")
                return

            # make SHA-512 hash of the code
            code_hash = hashlib.sha512(code_bytes).digest()
            self.log_debug(f"🔑 Code Hash: {code_hash.hex()}")
            self.animate_bubbles()

            #  generate KM||IV
            secret = get_random_bytes(32)
            self.KM = secret[:16]
            self.IV = secret[16:]
            self.log_debug(f"🔐 KM: {self.KM.hex()}")
            self.log_debug(f"🔐 IV: {self.IV.hex()}")

            #  encrypt KM||IV under server’s RSA
            cipher_rsa = PKCS1_OAEP.new(self.enc_pub_key)
            encrypted_km_iv = cipher_rsa.encrypt(secret)
            self.log_debug(f"🔒 Encrypted Keys: {encrypted_km_iv.hex()}")

            #  build final packet as: code_hash ∥ encrypted_km_iv ∥ student_id ∥ username
            if len(self.student_id) != 5:
                self.log_msg("❌ Student ID must be exactly 5 digits.")
                return

            final_msg = (
                code_hash
            + encrypted_km_iv
            + self.student_id.encode()
            + self.username.encode()
            )
            self.conn.sendall(final_msg)
            self.log_debug(f"📦 Final msg length: {len(final_msg)} bytes")
            self.log_msg("📤 Sent Final Reef Verification Message")

            # read and verify server’s “Authentication Successful” reply
            signature, message = self.read_signed_message()
            self.log_debug(f"📨 Final Result: {message.decode()}")

            if verify_signature(message, signature, self.sign_pub_key) and b"success" in message.lower():
                self.log_msg("🎉 Authentication successful — welcome to Atlantis!")
                self.animate_bubbles()
            else:
                self.log_msg("❌ Authentication failed. Return to surface.")

        except Exception as e:
            self.log_msg(f"🚨 Code verification error: {e}")

    def delete_account(self):
        """deletes an existing account"""
        if not self.conn:
            self.log_msg("⚠️ Dive in first (connect).")
            return

        try:
            self.conn.sendall(b"delete")
            self.log_msg("📤 Sent: delete")

            signature, message = self.read_signed_message()

            self.log_debug(f"📩 Delete Response: {message.decode()}")

            if not verify_signature(message, signature, self.sign_pub_key):
                self.log_msg("❌ Signature verification failed for delete ack.")
                return

            student_id = simpledialog.askstring("Student ID", "🐟 Enter your 5-digit diver ID:")
            username = simpledialog.askstring("Username", "🐚 Enter the shell name to delete:")


            combined = f"{student_id}{username}".encode()
            self.conn.sendall(combined)
            self.log_msg("📤 Sent ID + Username for deletion")

            signature, message = self.read_signed_message()

            self.log_debug(f"📩 Server Response: {message.decode()}")

            if b"success" not in message.lower():
                self.log_msg("❌ Deletion request failed: " + message.decode())
                return

            if not verify_signature(message, signature, self.sign_pub_key):
                self.log_msg("❌ Signature invalid for deletion ack.")
                return

            self.conn.sendall(b"rcode")
            self.log_msg("📤 Sent: rcode")

            signature, message = self.read_signed_message()


            if not verify_signature(message, signature, self.sign_pub_key):
                self.log_msg("❌ Signature invalid for rcode ack.")
                return

            rcode = simpledialog.askstring("Removal Code", "🐠 Enter the removal code received via email:")
            rcode_msg = f"{rcode}{student_id}{username}".encode()
            self.conn.sendall(rcode_msg)
            self.log_msg("📤 Sent final deletion message")

            signature, message = self.read_signed_message()

            if verify_signature(message, signature, self.sign_pub_key) and b"success" in message.lower():
                self.log_msg("✅ Account successfully deleted.")
            else:
                self.log_msg("❌ Final deletion failed or invalid signature.")

        except Exception as e:
            self.log_msg(f"⚠️ Deletion failed: {e}")
        
    
    def disconnect_from_server(self):
        """Close TCP connection and reset state."""
       
        if self.conn:
            try:
                self.conn.shutdown(socket.SHUT_RDWR)
                self.conn.close()
            except Exception:
                pass
            self.conn = None
            self.auth_success = False #clear the auth flag
            self.log_msg("🔴 Disconnected from server.")
        else:
            self.log_msg("⚠️ Already disconnected.")

        # clear UI state
        self.clear_animations()
        self.student_id    = None
        self.username      = None
        self.KM            = None
        self.IV            = None
        self.enc_pub_key   = None
        self.sign_pub_key  = None
        self.log_debug("🔑 Cleared loaded RSA public keys after disconnect.")
        



    def clear_animations(self):
        for bubble in self.bubbles:
            self.bubble_canvas.delete(bubble['id'])
        self.bubbles.clear()

        for fish in self.fishes:
            self.bubble_canvas.delete(fish['body'])
            self.bubble_canvas.delete(fish['tail'])
        self.fishes.clear()


        
    def on_close(self):
        """handler for window close: disconnect and destroy."""
        self.log_msg("⚓ Closing client window...")

        if self.conn:
            try:
                self.conn.shutdown(socket.SHUT_RDWR)
            except Exception:
                pass


            self.disconnect_from_server()

        self.clear_animations()
        self.master.destroy()

    def _recv_exact(self, n: int) -> bytes:
        """read exactly n bytes from socket or raise Connection Error."""
        buf = b''
        while len(buf) < n:
            chunk = self.conn.recv(n - len(buf))
            if not chunk:
                raise ConnectionError("Connection closed while reading")
            buf += chunk
        return buf

    def read_signed_message(self):
        """
        reads a fixed-size RSA signature, then reads the rest of the message until timeout.
        Returns (signature_bytes, message_bytes).
        """
        sig_len = self.sign_pub_key.size_in_bytes()

        # grab exactly the signature

        signature = self._recv_exact(sig_len)

        # then read until the socket pauses
        self.conn.settimeout(0.1)
        message = b''
        try:
            while True:
                chunk = self.conn.recv(4096)
                if not chunk:
                    break
                message += chunk
        except socket.timeout:
            pass
        finally:
            self.conn.settimeout(None)

        return signature, message




    def derive_iv(self, static_iv: bytes, sid: bytes) -> bytes:
        """
        Step-2 IV derivation:
        IV1 = SHA256(static_iv || SID)[:16]
        """
        h = SHA256.new(static_iv + sid).digest()
        return h[:16]


    def request_integrity_key(self):
        """
        Step 2: 
        1) Send A→S integrity-key request
        2) Receive C1‖C2‖SID (no separators)
        3) Slice off C1 and C2 by their known padded lengths
        4) Decrypt C1 under AES-CBC(KM, IV1), verify N1, extract KI
        """
        # 1) must have done Step-1
        if not getattr(self, "KM", None) or not getattr(self, "IV", None):
            self.log_msg("⚠️ Authenticate first (need KM & IV).")
            return

        # 2) pick a peer
        id_b   = simpledialog.askstring("Peer ID",       "Enter peer's 5-digit ID:")
        user_b = simpledialog.askstring("Peer Username", "Enter peer's username:")
        if not (id_b and user_b):
            return

        # 3) nonce N1
        N1 = get_random_bytes(16)
        self.N1 = N1

        # 4) send A→S: ID_A;username_A;ID_B;username_B;N1
        req = (
            self.student_id.encode() + b";" +
            self.username.encode()   + b";" +
            id_b.encode()            + b";" +
            user_b.encode()          + b";" +
            N1
        )
        self.conn.sendall(req)
        self.log_msg("📤 Sent integrity-key request")

        # 5) recv raw = C1||C2||SID (no separators any more)
        raw = self.conn.recv(4096)
        # AES-CBC pads to next 16-byte block:
        C1_len = 48  # e.g. 42B plaintext → padded to 48B
        C2_len = 32  # adjust if your C2 is a different fixed size
        if len(raw) < C1_len + C2_len:
            self.log_msg("❌ Integrity-key response too short.")
            return

        c1  = raw[:C1_len]
        c2  = raw[C1_len:C1_len + C2_len]  # you might use or verify this if needed
        sid = raw[C1_len + C2_len:]

        # 6) derive IV1 & decrypt C1
        iv1    = self.derive_iv(self.IV, sid)
        cipher = AES.new(self.KM, AES.MODE_CBC, iv1)
        P      = cipher.decrypt(c1)

        # 7) parse [KI(16) | IDA(5) | IDB(5) | N1(16)]
        ki      = P[:16]
        ida_b   = P[16:21]
        idb_b   = P[21:26]
        n1_recv = P[26:26+16]

        # 8) verify
        if ida_b.decode() != self.student_id or n1_recv != N1:
            self.log_msg("❌ Integrity-key response failed checks.")
            return

        # 9) success!
        self.KI = ki
        self.log_msg("✅ Integrity key received!")
        self.log_debug(f"🔑 KI: {ki.hex()}")
