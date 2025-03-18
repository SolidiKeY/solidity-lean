contract Bank {
    struct Account {
        int balance;
    }

    struct Person {
        Account account;
        int age;
    }

    Person alice;
    Person bob;

    function f() public {
        Person memory carol;
        bob = carol;
        assert(bob.account.balance == 0);

        alice = bob;
        alice.account.balance = 10;
        assert(bob.account.balance == 0);

        carol = alice;
        assert(carol.account.balance == 10);
    }
}
