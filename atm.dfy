class Card {
    var pin: nat;
    var balance: nat;

    constructor(pin: nat, balance: nat)
        requires 0 <= pin <= 9999
        requires balance >= 0
        ensures this.pin == pin
        ensures this.balance == balance
    {
        this.pin := pin;
        this.balance := balance;
    }
}


class ATM {
    const min_withdraw_amount: nat;
    const max_withdraw_amount: nat;
    const max_stored_amount: nat;

    var card: Card?;
    var entered_pin: int;
    var stored_amount: nat;

    constructor(min_withdraw_amount: nat, max_withdraw_amount: nat, initial_amount: nat, max_stored_amount: nat)
        requires 0 <= min_withdraw_amount <= max_withdraw_amount <= max_stored_amount
        requires 0 <= min_withdraw_amount <= initial_amount <= max_stored_amount
        ensures this.min_withdraw_amount == min_withdraw_amount
        ensures this.max_withdraw_amount == max_withdraw_amount
        ensures this.stored_amount == initial_amount
        ensures this.max_stored_amount == max_stored_amount
        ensures !IsCardInserted()
    {
        this.min_withdraw_amount := min_withdraw_amount;
        this.max_withdraw_amount := max_withdraw_amount;
        this.stored_amount := initial_amount;
        this.max_stored_amount := max_stored_amount;
        this.card := null;
        this.entered_pin := -1;
    }

    predicate IsCardInserted() reads this {
        this.card != null
    }

    predicate IsEnteredPINValid()
        requires IsCardInserted()
        reads this
        reads this.card
    {
        this.card.pin == this.entered_pin
    }

    predicate IsAddedStoredAmountValid(amount: nat) reads this {
        this.stored_amount + amount <= this.max_stored_amount
    }

    predicate IsWithdrawAmountValid(amount: nat)
        requires IsCardInserted()
        reads this
        reads this.card
    {
        && amount >= this.min_withdraw_amount
        && amount <= this.max_withdraw_amount
        && amount <= this.stored_amount
        && amount <= this.card.balance
    }

    method InsertCard(card: Card)
        requires !IsCardInserted()
        modifies this
        ensures IsCardInserted()
        ensures this.stored_amount == old(this.stored_amount)
        ensures this.entered_pin == old(this.entered_pin)
        ensures this.card == card
    {
        this.card := card;
    }
    
    method EjectCard()
        requires IsCardInserted()
        modifies this
        ensures !IsCardInserted()
        ensures this.stored_amount == old(this.stored_amount)
        ensures this.entered_pin == -1
        ensures this.card == null
    {
        this.card := null;
        this.entered_pin := -1;
    }

    method EnterPIN(pin: nat)
        requires IsCardInserted()
        modifies this
        ensures IsCardInserted()
        ensures this.stored_amount == old(this.stored_amount)
        ensures this.entered_pin == pin
        ensures this.card == old(this.card)
    {
        this.entered_pin := pin;
    }

    method ChangePIN(new_pin: nat)
        requires IsCardInserted()
        requires IsEnteredPINValid()
        modifies this, this.card
        ensures this.stored_amount == old(this.stored_amount)
        ensures this.card == old(this.card)
        ensures this.card.balance == old(this.card.balance)
        ensures this.card.pin == new_pin
        ensures this.entered_pin == new_pin
        ensures this.card.pin == this.entered_pin
    {
        this.card.pin := new_pin;
        this.entered_pin := new_pin;
    }

    method Withdraw(amount: nat)
        requires IsCardInserted()
        requires IsEnteredPINValid()
        requires IsWithdrawAmountValid(amount)
        modifies this, this.card
        ensures IsCardInserted()
        ensures this.stored_amount == old(this.stored_amount) - amount
        ensures this.card.balance == old(this.card.balance) - amount
        ensures this.card == old(this.card)
        ensures this.entered_pin == old(this.entered_pin)
        ensures IsEnteredPINValid()
    {
        this.stored_amount := this.stored_amount - amount;
        this.card.balance := this.card.balance - amount;
    }

    method Refill(amount: nat)
        requires !IsCardInserted()
        requires IsAddedStoredAmountValid(amount)
        modifies this
        ensures this.stored_amount == old(this.stored_amount) + amount
        ensures this.entered_pin == old(this.entered_pin)
        ensures !IsCardInserted()
    {
        this.stored_amount := this.stored_amount + amount;
    }
}

method Main() {
    var min_withdraw_amount := 10;
    var max_withdraw_amount := 100;
    var initial_amount := 200;
    var max_stored_amount := 400;
    var pin1 := 4242;
    var pin2 := 9999;
    var balance := 700;
    var atm := new ATM(min_withdraw_amount, max_withdraw_amount, initial_amount, max_stored_amount);
    var card1 := new Card(pin1, balance);
    var card2 := new Card(pin2, balance);

    atm.InsertCard(card1);
    atm.EnterPIN(pin1);

    atm.Withdraw(100);
    atm.Withdraw(100);

    atm.EjectCard();

    atm.Refill(400);
    
    atm.InsertCard(card2);
    atm.EnterPIN(pin2);

    atm.Withdraw(100);
    atm.Withdraw(100);
    atm.Withdraw(100);

    atm.EjectCard();

    atm.InsertCard(card1);
    atm.EnterPIN(pin1);
    atm.ChangePIN(8888);

    atm.Withdraw(100);
    atm.EjectCard();
}