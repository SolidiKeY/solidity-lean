# Balance representation

[Authoritative source](../../Solidity/Source/Monetary.lean).

Source accounts use natural balances. Any 256-bit word consumer therefore needs a proved fit/representation fact rather than silently truncating an arbitrary natural. Sender-funds validation and balance-range preservation do not discharge every cumulative affordability obligation for later calls.
