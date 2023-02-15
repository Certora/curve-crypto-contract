# @version 0.3.7
N_COINS: constant(uint256) = 3
A_MULTIPLIER: constant(uint256) = 100

@internal
@pure
def sort(A0: uint256[N_COINS]) -> uint256[N_COINS]:
    """
    Insertion sort from high to low
    """
    A: uint256[N_COINS] = A0
    for i in range(1, N_COINS):
        x: uint256 = A[i]
        cur: uint256 = i
        for j in range(N_COINS):
            y: uint256 = A[cur-1]
            if y > x:
                break
            A[cur] = y
            cur -= 1
            if cur == 0:
                break
        A[cur] = x
    return A


@external
@view
def pub_sort(A0: uint256[N_COINS]) -> uint256[N_COINS]:
    return self.sort(A0)


@external
@view
def pub_sort_noarray(a0: uint256, a1: uint256, a2: uint256) -> (uint256, uint256, uint256):
    A0 : uint256[N_COINS] = [ a0, a1, a2 ]
    B : uint256[N_COINS] = self.sort(A0)
    return B[0], B[1], B[2]


@internal
@view
def _geometric_mean(unsorted_x: uint256[N_COINS], sort: bool = True) -> uint256:
    """
    (x[0] * x[1] * ...) ** (1/N)
    """
    x: uint256[N_COINS] = unsorted_x
    if sort:
        x = self.sort(x)
    D: uint256 = x[0]
    diff: uint256 = 0
    for i in range(255):
        D_prev: uint256 = D
        tmp: uint256 = 10**18
        for _x in x:
            tmp = tmp * _x / D
        D = D * ((N_COINS - 1) * 10**18 + tmp) / (N_COINS * 10**18)
        if D > D_prev:
            diff = D - D_prev
        else:
            diff = D_prev - D
        if diff <= 1 or diff * 10**18 < D:
            return D
    raise "Did not converge"


@external
@view
def pub_geometric_mean(a0: uint256, a1: uint256, a2: uint256) -> uint256:
    A0 : uint256[N_COINS] = [ a0, a1, a2 ]
    return self._geometric_mean(A0)
