void main(int x, int y, int n)
{
	x = 6;
	y = 4;
    n = -2;

    int band;
    band = x & y;

    int bor;
    bor = x | y;

    int bxor;
    bxor = x ^ y;

    int moda;
    int modb;
    int modn;
    moda = x % y;
    modb = y % x;
    modn = n % y;

    int un;
    un = +(-(x--5));

    assert(band == 4);
    assert(bor == 6);
    assert(bxor == 2);
    assert(moda == 2);
    assert(modb == 4);
    assert(modn == 2);
    assert(un == -11);
}
