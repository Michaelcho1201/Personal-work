from ppm_process import process, scale


def main():
    # test process
    print("*** testing process ***")
    file_in = open("files/small.ppm", "r")
    file_in.readline()
    file_in.readline()
    file_in.readline()
    assert type(process(file_in.readlines(), 4, 6)) == list
    file_in = open("files/small.ppm", "r")
    file_in.readline()
    file_in.readline()
    file_in.readline()
    assert process(file_in.readlines(), 4, 6) == [[255, 0, 0, 0, 255, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 255, 0, 0],
                                                  [0, 255, 0, 0, 0, 255, 255, 0, 255, 0, 0, 0, 255, 0, 0, 0, 255, 0],
                                                  [0, 255, 255, 255, 0, 255, 0, 0, 0, 255, 0, 0, 255, 0, 0, 0, 255, 0],
                                                  [0, 0, 255, 255, 255, 255, 0, 0, 0, 255, 0, 0, 0, 255, 0, 0, 0, 255]]
    file_in = open("files/small.ppm", "r")
    file_in.readline()
    file_in.readline()
    file_in.readline()
    assert process(file_in.readlines(), 6, 4) == [[255, 0, 0, 0, 255, 0, 0, 0, 255, 255, 255, 255],
                                                  [0, 0, 0, 255, 0, 0, 0, 255, 0, 0, 0, 255],
                                                  [255, 0, 255, 0, 0, 0, 255, 0, 0, 0, 255, 0],
                                                  [0, 255, 255, 255, 0, 255, 0, 0, 0, 255, 0, 0],
                                                  [255, 0, 0, 0, 255, 0, 0, 0, 255, 255, 255, 255],
                                                  [0, 0, 0, 255, 0, 0, 0, 255, 0, 0, 0, 255]]
    print("process passed")

    # test scale
    print("*** testing scale ***")
    # TODO: add test cases to thoroughly test this function
    image = [[255, 0, 0, 0, 255, 0, 0, 0, 255, 255, 255, 255], [0, 0, 0, 255, 0, 0, 0, 255, 0, 0, 0, 255],
             [255, 0, 255, 0, 0, 0, 255, 0, 0, 0, 255, 0], [0, 255, 255, 255, 0, 255, 0, 0, 0, 255, 0, 0],
             [255, 0, 0, 0, 255, 0, 0, 0, 255, 255, 255, 255], [0, 0, 0, 255, 0, 0, 0, 255, 0, 0, 0, 255]]
    assert type(scale(image, 3, 1)) == list
    assert scale(image, 3, 1) == [[255, 0, 0, 0, 255, 0, 0, 0, 255, 255, 255, 255],
                                  [0, 255, 255, 255, 0, 255, 0, 0, 0, 255, 0, 0]]
    assert scale(image, 3, 2) == [[255, 0, 0, 0, 0, 255],
                                  [0, 255, 255, 0, 0, 0]]
    print("scale passed")


if __name__ == "__main__":
    main()
