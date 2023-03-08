methods {
    mybalance() returns uint256 envfree
    totalSupply() returns uint256 envfree
    balanceOf(address) returns uint256 envfree
    transfer(address, uint256) returns bool
    transferFrom(address, address, uint256) returns bool

    default() => HAVOC_ECF;
}

ghost uint256 totalTokens;

invariant contract_is_liquid()
  mybalance() == totalSupply()
  { preserved with (env e) { require e.msg.sender != currentContract; } }

invariant contract_is_liquid_ghost()
  mybalance() == totalTokens
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
    uint256 senderBefore = balanceOf@withrevert(e.msg.sender);
    assert !lastReverted;
    uint256 recvBefore = balanceOf@withrevert(to);
    assert !lastReverted;
    uint256 otherBefore = balanceOf@withrevert(other);
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
    uint256 otherBefore = balanceOf@withrevert(other);
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
    uint256 senderBefore = balanceOf@withrevert(from);
    assert !lastReverted;
    uint256 recvBefore = balanceOf@withrevert(to);
    assert !lastReverted;
    uint256 otherBefore = balanceOf@withrevert(other);
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
    uint256 otherBefore = balanceOf@withrevert(other);
    assert !lastReverted;
    transferFrom(e, from, to, value);
    assert to_mathint(balanceOf@withrevert(other)) == otherBefore;
}
