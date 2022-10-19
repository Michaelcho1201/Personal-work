numbers = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
for d in range(len(numbers)):
    if d % 2 != 0:
        odd_numbers = [d]
        print(odd_numbers)

numbers = [4, 5, 6, 7]
for i in numbers:
    print(i)
for i in range(len(numbers)):
    numbers[i] = i * 2
print(numbers)


