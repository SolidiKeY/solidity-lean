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
        alice.account.balance = 10;

        Person memory carol;
        carol.account.balance = 20;

        carol = alice;
    }
}
