
void main(int a)
{
	a = 2;
	int b;
	b = 1;

	if (a==2 && a==b+1){
	    a=3;
	}

    assert(a != 2);
    assert(a == 3);
}