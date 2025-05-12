import tkinter as tk
from client_gui import ClientGUI

def main():
    root = tk.Tk()
    gui = ClientGUI(root)
    root.mainloop()

    

if __name__ == "__main__":
    main()
