void main(int i, int j, int k)
{
	i=36;
	j=4;
	k=-128;

	int p;
	int q;
	int r;
	int s;

	p = i >> j;
	q = k >> j;
    r = k << j;
    s = i << j;

    assert(p == 2);
    assert(q == -8);
    assert(r == -2048);
    assert(s == 576);
}
