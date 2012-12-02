void main()
{

    int x;
    int y;
	x = 8;
	y = 4;
    int n ;
    n = -8;


    int add;
    add = x + y;

    int band;
    band = x & y;

    int bor;
    bor = x | y;

    int bxor;
    bxor = x ^ y;

    int div;
    div = x / y;

    int lsft;
    lsft =   x << y;

    int lsftn;
    lsftn = n << y;

    int mod ;
    int modn;
    mod = x % y ;
    modn = n % y;

    int sub;
    sub = x - y;

    assert (  add == 12);
    assert (  band == 4);
    assert (  bor == 12);
    assert (  bxor == 12);
    assert (  div == 2);
    assert (  lsft == 128);
    assert (  lsftn == -128);

    assert ( sub == 4);

}
