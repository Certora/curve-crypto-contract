methods {
    pub_sort(uint256[3]) returns (uint256[3]) envfree
    pub_sort_noarray(uint256,uint256,uint256) returns (uint256,uint256,uint256) envfree
    pub_geometric_mean(uint256,uint256,uint256) returns uint256 envfree
    reduction_coefficient(uint256[3], uint256) returns uint256 envfree
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
    uint256 a0; uint256 a1; uint256 a2;

    uint256 b0;
    uint256 b1;
    uint256 b2;
    b0, b1, b2 = pub_sort_noarray(a0,a1,a2);

    assert b0 >= b1;
    assert b1 >= b2;
}

rule sort_permutes {
    uint256 a0;
    uint256 a1;
    uint256 a2;

    uint256 b0;
    uint256 b1;
    uint256 b2;
    b0, b1, b2 = pub_sort_noarray(a0,a1,a2);

    // Specifying that the arrays permutes needs ghost function for the permutation.
    // In this contract all we care about is that the sum and the product of the values
    // don't change since the invariant only uses that.

    assert a0*a1*a2 == b0*b1*b2;
    assert a0+a1+a2 == b0+b1+b2;
}

rule sort_permutes_full {
    uint256 a0;
    uint256 a1;
    uint256 a2;

    uint256 b0;
    uint256 b1;
    uint256 b2;
    mathint x;
    b0, b1, b2 = pub_sort_noarray(a0,a1,a2);

    // Trick to check for permutation:  Since we don't restrict x, we show that the
    // polynomials are equal for all x.  This implies that this is a correct permutation.

    assert (a0-x)*(a1-x)*(a2-x) == (b0-x)*(b1-x)*(b2-x);
}

rule geometric_mean {
    uint256 a0;
    uint256 a1;
    uint256 a2;

    uint256 b;
    require a0 > 0 && a1 > 0 && a2 >0;
    b = pub_geometric_mean(a0,a1,a2);

    //assert b >= a0 || b >= a1 || b >= a2;
    assert (b-1) * (b-1) * (b-1) * 999999999999999999 <= a0 * a1 * a2 * 1000000000000000000;
    assert (b+1) * (b+1) * (b+1) * 1000000000000000000 >= a0 * a1 * a2 * 999999999999999999;
    //assert b*1000000000000000000 >= a0*999999999999999999 || b*1000000000000000000 >= a1*999999999999999999 || b*1000000000000000000 >= a2*999999999999999999;
    //assert (b-1)*1000000000000000000 <= a0*1000000000000000001 || b*1000000000000000000 <= a1*1000000000000000001 || b*1000000000000000000 <= a2*1000000000000000001;
    //assert b*b*b <= a0*a1*a2;
    //assert a0*a1*a2 < (b+1)*(b+1)*(b+1);
}

rule reduction_coeff_ok {
    uint256[3] xyz;
    uint256 x = xyz[0];
    uint256 y = xyz[1];
    uint256 z = xyz[2];
    uint256 gamma;
    uint256 coeff;
    
    coeff = reduction_coefficient(xyz, gamma);
    //assert coeff <= 1000000000000000000;
    mathint sum = (x+y+z);
    mathint firstKnum = 3*3*3 * x*y*z;
    mathint firstKdenom =  sum*sum*sum;
    mathint Knum;
    mathint Kdenom;
    if (gamma > 0) {
        require Knum == firstKdenom * gamma;
        require Kdenom == (Knum + (firstKdenom - firstKnum) * 1000000000000000000);
    } else {
        require Knum == firstKnum;
        require Kdenom == firstKdenom;
    }
    mathint coeffMinusK = Kdenom * coeff - Knum*1000000000000000000;
    assert coeffMinusK <= 1000000 * Kdenom;
    assert 0 - coeffMinusK <= 10000000 * Kdenom;
}