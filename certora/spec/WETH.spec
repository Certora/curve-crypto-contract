methods {
    function mybalance() external returns uint256 envfree;
    function totalSupply() external returns uint256 envfree;
    function balanceOf(address) external returns uint256 envfree;
    //function transfer(address, uint256) external returns bool;
    //function transferFrom(address, address, uint256) external returns bool;

    function _.default() external => HAVOC_ECF;
}

ghost mathint totalTokens;

invariant contract_is_liquid()
  mybalance() == totalSupply()
  { preserved with (env e) { require e.msg.sender != currentContract; } }

invariant contract_is_liquid_ghost()
  to_mathint(mybalance()) == totalTokens
  { preserved with (env e) { require e.msg.sender != currentContract; } }

hook Sstore balanceOf[KEY address adr] uint256 v (uint256 vold) STORAGE {
   totalTokens = totalTokens + v - vold;
}

rule depositSatisfiesInvariantAlmost()
{
    env e;
    require mybalance() == totalSupply();
    require e.msg.sender != currentContract;
    deposit(e);
    assert mybalance() == totalSupply();
}

rule withdrawSatisfiesInvariantAlmost()
{
    env e;
    uint256 amount;
    require mybalance() == totalSupply();
    require e.msg.sender != currentContract;
    withdraw(e, amount);
    assert mybalance() == totalSupply();
}

rule testTransfer() {
    env e;
    address to;
    address other;
    uint256 value;

    require e.msg.sender!= to;
    require other != to;
    require other != e.msg.sender;
    mathint senderBefore = balanceOf@withrevert(e.msg.sender);
    assert !lastReverted;
    mathint recvBefore = balanceOf@withrevert(to);
    assert !lastReverted;
    mathint otherBefore = balanceOf@withrevert(other);
    assert !lastReverted;
    transfer(e, to, value);

    assert to_mathint(balanceOf@withrevert(e.msg.sender)) == senderBefore - value;
    assert to_mathint(balanceOf@withrevert(to)) == recvBefore + value;
    assert to_mathint(balanceOf@withrevert(other)) == otherBefore;
}

rule testTransferSelf() {
    env e;
    address other;
    uint256 value;
    address to = e.msg.sender;

    /* we check that all balances do not change, other can be any account,
     * even the sender.
     */
    mathint otherBefore = balanceOf@withrevert(other);
    assert !lastReverted;
    transfer(e, to, value);
    assert to_mathint(balanceOf@withrevert(other)) == otherBefore;
}

rule testTransferFromDifferent() {
    env e;
    address from;
    address to;
    address other;
    uint256 value;

    require from != to;
    require other != to;
    require other != from;
    mathint senderBefore = balanceOf@withrevert(from);
    assert !lastReverted;
    mathint recvBefore = balanceOf@withrevert(to);
    assert !lastReverted;
    mathint otherBefore = balanceOf@withrevert(other);
    assert !lastReverted;
    transferFrom(e, from, to, value);

    assert to_mathint(balanceOf@withrevert(from)) == senderBefore - value;
    assert to_mathint(balanceOf@withrevert(to)) == recvBefore + value;
    assert to_mathint(balanceOf@withrevert(other)) == otherBefore;
}

rule testTransferFromSame() {
    env e;
    address from;
    address to;
    address other;
    uint256 value;

    require from == to;
    /* we check that all balances do not change, other can be any account,
     * even from or to.
     */
    mathint otherBefore = balanceOf@withrevert(other);
    assert !lastReverted;
    transferFrom(e, from, to, value);
    assert to_mathint(balanceOf@withrevert(other)) == otherBefore;
}
