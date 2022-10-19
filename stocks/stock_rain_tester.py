from stock_rain import parse_rainfall, date_change, parse_stock, correlate_data, scatter_plot


def parse_rainfall_tester():
    """
    Run a series of tests for parse_rainfall
    :return (boolean): were all tests successful
    """
    assert parse_rainfall("csvs/rainTest.csv") == {'2012-01-01': 0.0,
                                                   '2012-01-02': 0.43,
                                                   '2012-01-03': 0.03,
                                                   '2012-01-04': 0.8,
                                                   '2012-01-05': 0.05,
                                                   '2012-01-06': 0.1,
                                                   '2012-01-07': 0.0,
                                                   '2012-01-08': 0.0,
                                                   '2012-01-09': 0.17}

    rainfall_data = parse_rainfall("csvs/rainSeattle-1948-2017.csv")
    for key, value in rainfall_data.items():
        # check the data type of return values
        assert type(key) == str
        assert type(value) == float

        # check the date format of return value
        date = key.split('-')
        year, month, day = date[0], date[1], date[2]

        if len(year) != 4:
            print("The YEAR format of parse_rainfall's return value is incorrect")
            return False
        elif len(month) != 2:
            print("The MONTH format of parse_rainfall's return value is incorrect")
            return False
        elif len(day) != 2:
            print("The DAY format of parse_rainfall's return value is incorrect")
            return False

    return True


def parse_stock_tester():
    """
    Run a series of tests for parse_stock
    :return (boolean): were all tests successful
    """
    assert parse_stock("csvs/stockTest.csv", 'GOOGL') == {'2012-01-03': 6.24,
                                                          '2012-01-04': 1.62,
                                                          '2012-01-05': -1.57,
                                                          '2012-01-06': -4.56,
                                                          '2012-01-09': -12.03}

    stock = "MMM"
    stock_data = parse_stock("csvs/stocks-2006-2017.csv", stock)
    for key, value in stock_data.items():
        # check the data type of return value
        assert type(key) == str
        assert type(value) == float

        # check the date format of return value
        date = key.split('-')
        year, month, day = date[0], date[1], date[2]

        if len(year) != 4:
            print(year, "The YEAR format of parse_stock's return value is incorrect")
            return False
        elif len(month) != 2:
            print("The MONTH format of parse_stock's return value is incorrect")
            return False
        elif len(day) != 2:
            print("The DAY format of parse_stock's return value is incorrect")
            return False

    return True


def main():
    """
    For testing purposes
    """
    # Part 1 Testing
    print("Testing date_change function")
    assert type(date_change("1/3/2011")) == str
    assert date_change("1/10/2011") == "2011-01-10"
    assert date_change("11/10/2011") == "2011-11-10"
    print("PASS")

    print("")
    print("testing parse_rainfall ... ")
    print("PASS" if parse_rainfall_tester() else "FAIL")


    print("")
    print("testing parse_stock ... ")
    print("PASS" if parse_stock_tester() else "FAIL")


    rainfall_data = parse_rainfall("csvs/rainSeattle-1948-2017.csv")
    stock = "MMM"
    stock_data = parse_stock("csvs/stocks-2006-2017.csv",stock)
    data = correlate_data(stock_data, rainfall_data)
    scatter_plot(data, 'b+', stock, False)

    stock = "JNJ"
    stock_data = parse_stock("csvs/stocks-2006-2017.csv",stock)
    data = correlate_data(stock_data, rainfall_data)
    scatter_plot(data, 'r.', stock, True)


if __name__ == "__main__":
    main()
