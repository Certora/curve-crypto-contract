methods {
    pub_sort(uint256[3]) returns (uint256[3]) envfree
    pub_sort_noarray(uint256,uint256,uint256) returns (uint256,uint256,uint256) envfree
    pub_geometric_mean(uint256,uint256,uint256) returns uint256 envfree
}

/*
rule sort_sorts_arr {
    uint256[3] A;
    uint256[3] B;

    B = pub_sort(A);

    assert B[0] >= B[1];
    assert B[1] >= B[2];
}
*/

rule sort_sorts {
    uint256 a0;
    uint256 a1;
    uint256 a2;

    uint256 b0;
    uint256 b1;
    uint256 b2;
    b0, b1, b2 = pub_sort_noarray(a0,a1,a2);

    assert b0 >= b1;
    assert b1 >= b2;
}

rule geometric_mean {
    uint256 a0;
    uint256 a1;
    uint256 a2;

    uint256 b;
//    require a0 > 1 && a1 > 1 && a2 > 1;
    b = pub_geometric_mean(a0,a1,a2);

    assert b >= a0;
    assert b*1000000000000000000 >= a0*999999999999999999 || b*1000000000000000000 >= a1*999999999999999999 || b*1000000000000000000 >= a2*999999999999999999;
    assert b*1000000000000000000 <= a0*1000000000000000001 || b*1000000000000000000 <= a1*1000000000000000001 || b*1000000000000000000 <= a2*1000000000000000001;
    //assert b*b*b <= a0*a1*a2;
    //assert a0*a1*a2 < (b+1)*(b+1)*(b+1);
}
