
void main(int a)
{
	a = 2;
	int b;
	havoc(b);

	if (a==b){
	    a=3;
	}

    assert(a == 2);
    assert(a != 3);
}