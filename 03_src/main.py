class ShowInt:
    def __init__(self, int_value):
        self.value = int_value
        print("Int型の値を表示します：")
        print(f"{str(int_value)}:{type(int_value)}")


v = ShowInt(100)
v.value = 200