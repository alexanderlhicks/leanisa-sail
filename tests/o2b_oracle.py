"""Small independent GF(2^64)[y]/(y^3+y+1) candidate oracle."""

MASK = (1 << 64) - 1


def kmul(a: int, b: int) -> int:
    product = 0
    for bit in range(64):
        if (b >> bit) & 1:
            product ^= a << bit
    for bit in range(126, 63, -1):
        if (product >> bit) & 1:
            product ^= (1 << bit) | (0x1B << (bit - 64))
    return product & MASK


def emul(a: int, b: int) -> int:
    aa = [(a >> (64 * i)) & MASK for i in range(3)]
    bb = [(b >> (64 * i)) & MASK for i in range(3)]
    coefficients = [0] * 5
    for i in range(3):
        for j in range(3):
            coefficients[i + j] ^= kmul(aa[i], bb[j])
    # y^3 = y+1, y^4 = y^2+y.
    return ((coefficients[0] ^ coefficients[3]) |
            ((coefficients[1] ^ coefficients[3] ^ coefficients[4]) << 64) |
            ((coefficients[2] ^ coefficients[4]) << 128))


def choose(roots: tuple[int, int, int], fixed: dict[int, int],
           plans: list[tuple[int | None, int | None]]) -> tuple[int, int, int, int] | None:
    """Return first passing ordinal and A/B/product, using virtual root IDs."""
    ra, rb, rc = roots
    for ordinal, (candidate_a, candidate_b) in enumerate(plans):
        values = dict(fixed)
        valid = True
        for root, value in ((ra, candidate_a), (rb, candidate_b)):
            if value is None:
                continue
            if root in fixed or root in values and values[root] != value:
                valid = False
                break
            values[root] = value
        if not valid:
            continue
        values.setdefault(ra, 0)
        values.setdefault(rb, 0)
        product = emul(values[ra], values[rb])
        if rc in values and values[rc] != product:
            continue
        return ordinal, values[ra], values[rb], product
    return None
