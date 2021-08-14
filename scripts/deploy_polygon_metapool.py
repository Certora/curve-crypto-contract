import requests
from brownie import (
    accounts,
    CurveCryptoMath3,
    CurveTokenV4,
    CurveCryptoViews3,
    CurveCryptoSwapMatic,
    ERC20Mock,
    ZapAave,
    compile_source,
)
from brownie import interface
import json

# Addresses are taken for Matic
COINS = [
    "0xE7a24EF0C5e95Ffb0f6684b813A78F2a3AD7D171",  # am3Crv
    "0x5c2ed810328349100A66B82b78a1791B101C9D61",  # amWBTC
    "0x28424507fefb6f7f8E9D3860F56504E4e5f5f390"   # amWETH
]
SWAP = "0x445FE580eF8d70FF569aB36e80c647af338db351"
FEE_RECEIVER = "0xA237034249290De2B07988Ac64b96f22c0E76fE0"
MATIC_RECEIVER = "0x19793B454D3AfC7b454F206Ffe95aDE26cA6912c"


def main():
    p = requests.get("https://api.coingecko.com/api/v3/simple/price?ids=bitcoin,ethereum&vs_currencies=usd").json()
    INITIAL_PRICES = [int(p[cur]['usd'] * 1e18) for cur in ['bitcoin', 'ethereum']]
    txparams = {"from": accounts[0], 'required_confs': 5}

    crypto_math = CurveCryptoMath3.deploy(txparams)
    token = CurveTokenV4.deploy("Curve USD-BTC-ETH", "crvUSDBTCETH", txparams)

    if COINS:
        coins = [interface.ERC20(addr) for addr in COINS]
        vprice = interface.Swap(SWAP).get_virtual_price()
        INITIAL_PRICES = [p * 10**18 // vprice for p in INITIAL_PRICES]
    else:
        coins = [
            ERC20Mock.deploy(name, name, 18, txparams) for name in ["USD", "BTC", "ETH"]
        ]

    source = CurveCryptoViews3._build["source"]
    source = source.replace("1,#0", str(10 ** (18 - coins[0].decimals())) + ',')
    source = source.replace("1,#1", str(10 ** (18 - coins[1].decimals())) + ',')
    source = source.replace("1,#2", str(10 ** (18 - coins[2].decimals())) + ',')
    deployer = compile_source(source, vyper_version="0.2.12").Vyper
    crypto_views = deployer.deploy(crypto_math, txparams)

    source = CurveCryptoSwapMatic._build["source"]
    source = source.replace("0x0000000000000000000000000000000000000000", crypto_math.address)
    source = source.replace("0x0000000000000000000000000000000000000001", token.address)
    source = source.replace("0x0000000000000000000000000000000000000002", crypto_views.address)
    source = source.replace("0x0000000000000000000000000000000000000010", coins[0].address)
    source = source.replace("0x0000000000000000000000000000000000000011", coins[1].address)
    source = source.replace("0x0000000000000000000000000000000000000012", coins[2].address)
    source = source.replace("1,#0", str(10 ** (18 - coins[0].decimals())) + ',')
    source = source.replace("1,#1", str(10 ** (18 - coins[1].decimals())) + ',')
    source = source.replace("1,#2", str(10 ** (18 - coins[2].decimals())) + ',')
    deployer = compile_source(source, vyper_version="0.2.12").Vyper

    swap = deployer.deploy(
        accounts[0],
        FEE_RECEIVER,
        int(0.2 * 3 ** 3 * 10000),  # A
        int(2.8e-4 * 1e18),  # gamma
        int(1.1e-3 * 1e10),  # mid_fee
        int(4.5e-3 * 1e10),  # out_fee
        2 * 10**12,  # allowed_extra_profit
        int(5e-4 * 1e18),  # fee_gamma
        int(0.002 * 1e18),  # adjustment_step
        5 * 10**9,  # admin_fee
        600,  # ma_half_time
        INITIAL_PRICES,
        txparams,
    )
    token.set_minter(swap, txparams)
    swap.set_reward_receiver(MATIC_RECEIVER, txparams)

    zap = ZapAave.deploy(swap.address, SWAP, txparams)

    print("Swap address:", swap.address)
    print("Token address:", token.address)
    print("Zap address:", zap.address)

    with open("swap.json", "w") as f:
        json.dump(swap.abi, f)

    with open("token.json", "w") as f:
        json.dump(token.abi, f)

    with open("zap.json", "w") as f:
        json.dump(zap.abi, f)

    return swap, token, zap
