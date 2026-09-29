import time
import json
import base64
import urllib.request
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import padding
from cryptography.hazmat.primitives.serialization import load_pem_private_key

# --- YOUR API CREDENTIALS (Synced from bot.py) ---
KEY_ID = "61d31577-0d62-4c6d-9c34-eb37e61202a1"
PRIVATE_KEY_PATH = "private_key.pem"
DEMO_MODE = False  # Set to True for Sandbox, False for Live

HOST = "https://external-api.demo.kalshi.co/trade-api/v2" if DEMO_MODE else "https://external-api.kalshi.com/trade-api/v2"

def load_private_key():
    with open(PRIVATE_KEY_PATH, "rb") as key_file:
        return load_pem_private_key(key_file.read(), password=None)

def sign_request(private_key, timestamp_str, method, path):
    msg = f"{timestamp_str}{method}{path}".encode("utf-8")
    signature = private_key.sign(
        msg,
        padding.PSS(
            mgf=padding.MGF1(hashes.SHA256()),
            salt_length=padding.PSS.MAX_LENGTH
        ),
        hashes.SHA256()
    )
    return base64.b64encode(signature).decode("utf-8")

def kalshi_request(method, endpoint, payload=None):
    url = f"{HOST}{endpoint}"
    timestamp_str = str(int(time.time() * 1000))
    path = f"/trade-api/v2{endpoint}"
    
    private_key = load_private_key()
    sig = sign_request(private_key, timestamp_str, method, path)
    
    headers = {
        "Content-Type": "application/json",
        "Accept": "application/json",
        "KALSHI-ACCESS-KEY": KEY_ID,
        "KALSHI-ACCESS-TIMESTAMP": timestamp_str,
        "KALSHI-ACCESS-SIGNATURE": sig
    }
    
    data = json.dumps(payload).encode("utf-8") if payload else None
    req = urllib.request.Request(url, data=data, headers=headers, method=method)
    
    try:
        with urllib.request.urlopen(req) as response:
            return json.loads(response.read().decode())
    except urllib.error.HTTPError as e:
        print(f"--> [HTTP {e.code}] Error Response: {e.read().decode()}")
        raise e

def allocate_funds_to_shard_2():
    print("--> Fetching current portfolio balance breakdown...")
    try:
        balance_data = kalshi_request("GET", "/portfolio/balance")
        print(f"Current Balance Configuration:\n{json.dumps(balance_data, indent=2)}")
    except Exception as e:
        print(f"[!] Could not fetch pre-allocation balance: {e}")

    print("\n--> Requesting 100% allocation shift to Shard 2...")
    endpoint = "/portfolio/target_balance_allocation"
    
    # Allocating 100% of the account value specifically to Shard 2 (Crypto/Commodities)
    payload = {
        "allocations": [
            {"exchange_index": 2, "percent": 100}
        ]
    }
    
    try:
        response = kalshi_request("POST", endpoint, payload=payload)
        print("[SUCCESS] Target balance allocation updated successfully!")
        
        print("\n--> Waiting 3 seconds for the clearing engine to rebalance...")
        time.sleep(3)
        
        updated_balance = kalshi_request("GET", "/portfolio/balance")
        print(f"Updated Balance Configuration:\n{json.dumps(updated_balance, indent=2)}")
        return response
    except Exception as e:
        print(f"[ERROR] Failed to update target allocation: {e}")
        return None

if __name__ == "__main__":
    print(f"--- Kalshi Shard Allocation Utility | Environment: {'DEMO' if DEMO_MODE else 'LIVE'} ---")
    allocate_funds_to_shard_2()
