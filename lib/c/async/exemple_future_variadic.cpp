
template <typename T>
struct c {
	T x;
};

template <typename ... TS>
class cs {
	public:
	void f (c<TS>... a) {
	}
};

int main () {
	cs<int,float> o;
	c<int> o1 = {4};
	c<float> o2 = {3.0};
	o.f(o1,o2);
}
