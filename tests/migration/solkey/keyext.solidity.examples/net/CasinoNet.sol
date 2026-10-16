// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

// Casino (SolidityCalculus/SimpleCasino) in the supported fragment. The course ships no
// .key obligations for it, so the invariant here is our own money-conservation one over
// the net ledger (the casino-*.key problems beside this file):
//   state != BET_PLACED -> net(operator) + net(player) == pot,
//   state == BET_PLACED -> net(operator) + net(player) == pot + bet.
// decideBet resolves by the parity of the revealed secret and pays the win with the
// transfer LAST, so the invariant also holds at the payout point
// (casino-decideBet-withcallback.key).
contract CasinoNet {
    address payable operator;
    address payable player;
    uint pot;
    uint bet;
    uint guess; // 0 HEADS, 1 TAILS
    uint state; // 1 game open, 2 bet placed

    function addToPot() public payable {
        address op = operator;
        require(msg.sender == op);
        require(state == 1);
        uint p = pot;
        pot = p + msg.value;
    }

    function placeBet(uint g) public payable {
        address pl = player;
        require(msg.sender == pl);
        require(state == 1);
        uint p = pot;
        require(msg.value <= p);
        bet = msg.value;
        guess = g;
        state = 2;
    }

    function decideBet(uint secret) public {
        address op = operator;
        require(msg.sender == op);
        require(state == 2);
        state = 1;
        uint b = bet;
        bet = 0;
        uint coin = secret % 2;
        uint g = guess;
        if (coin == g) {
            uint p = pot;
            pot = p - b;
            uint win = 2 * b;
            player.transfer(win);
        } else {
            uint p = pot;
            pot = p + b;
        }
    }
}
