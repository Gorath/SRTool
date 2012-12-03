void main(int i, int j, int k)
{
	i=2;
	j=4;
	k=4;

	int p;
	int q;
	int r;

	p = (i < j) || (i > j);
	q = (j == k);
	r = (p && q) ;

    assert(p);
    assert(q);
	assert(r);
}
