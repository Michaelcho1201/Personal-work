"""
    CS051P Lab Assignments: Stock v.s. Rain

    Author: Michael Cho. 

    Date:   4/24/2020

    The goal of this assignment is to familiarize you with data analysis
    and visualization. You'll practice handling files in csv format,
    create and manipulate Python dictionaries, and do some basic plotting
    using the matplotlib package.
"""
from string import*
import matplotlib.pyplot as plt
import sys


def parse_rainfall(fname):
    """
    Takes a csv data sheet with filename fname and creates a dictionary with dates as keys and the amount of inches
    of precipitation as values. It skips data entries with no recorded rain data.
    :param fname: (str) A filename of any data sheet with date and amount of rain in inches.
    :return: (dict) a dictionary with dates as values and amount of rain in inches.
    """
    # Sets rain_dict as empty dictionary
    rain_dicts = {}

    # Opens the file and reads the name header.
    with open(fname, 'r') as rain_data:
        rain_data.readline()

        # Uses for loop to make a list for each line.
        for line in rain_data.readlines():
            new_line = line.rstrip("\n")
            rain_list = new_line.split(",")
            na_check = rain_list[4]

            # Prevents any non recorded days from being imputed into the dictionary.
            if na_check.strip('"') != 'NA':
                # Takes the date from list as keys and takes the amount of rain in inches from list as values.
                date = str(rain_list[0])
                key_date = date.strip('"')
                precip_data = rain_list[1]
                rain_dicts[key_date] = float(precip_data)

        # Returns the dictionary.
        return rain_dicts


def date_change(date):
    """
    Changes the date from month/day/year to year-month-day, adding zeros for one digit days and months.
    :param date: (str) a string that represents a date in month/day/year
    :return: (str) an string that is a date in year-month-day.
    """
    # Turns the string into a list and indexes each value of list.
    list_date = date.split('/')
    year = list_date[2]
    month = list_date[0]
    day = list_date[1]

    # Adds zero to day and/or month if day and/or month are single digits.
    if int(month) < 10 and int(day) < 10:
        date = year + "-0" + month + "-0" + day
    elif int(month) >= 10 and int(day) < 10:
        date = year + "-" + month + "-0" + day
    elif int(month) < 10 and int(day) >= 10:
        date = year + "-0" + month + "-" + day
    else:
        date = year + "-" + month + "-" + day

    # Returns the date.
    return date


def parse_stock(fname, sym):
    """
    Takes a csv filename of stock data named fname and a symbol of stock data named sym and creates a dictionary with
    dates as keys and the change in stock as values from data inputs that have sym.
    :param fname: (str) any filename of stock data
    :param sym: (str) any stock symbol.
    :return: (dict) a dictionary with dates as keys and change in stock as values from data inputs containing sym.
    """
    # Sets stock_dict as empty dictionary.
    stock_dicts = {}

    # Opens filename and reads header line.
    with open(fname, 'r') as stock_data:
        stock_data.readline()

        # Uses for loop to turn each remaining line into list.
        for line in stock_data.readlines():
            new_line = line.rstrip("\n")
            stock_list = new_line.split(",")

            # Prevents data inputs with no opening and/or closing values and passes inputs with no sym.
            if stock_list[1] != '':
                if stock_list[4] != '':
                    if sym == stock_list[6]:

                        # Takes the old /date and changes it using function date_change.
                        old_date = stock_list[0]
                        new_date = date_change(old_date)

                        # Indexes opening and closing values, turns them into floats then times them by 100, and int() them.
                        stock_close = int(float(stock_list[4]) * 100)
                        stock_open = int(float(stock_list[1]) * 100)

                        # Checks for and undoes any unnecessary rounding done by float()
                        while not stock_close / 100 == float(stock_list[4]):
                            if stock_close / 100 < float(stock_list[4]):
                                stock_close = stock_close + 1
                            else:
                                stock_close = stock_close - 1
                        while not stock_open / 100 == float(stock_list[1]):
                            if stock_open / 100 < float(stock_list[1]):
                                stock_open = stock_open + 1
                            else:
                                stock_open = stock_open - 1

                        # Subtracts stock_open from stock_close and divides them by 100.
                        stock_change = (stock_close - stock_open) / 100
                        stock_dicts[new_date] = stock_change
                    else:
                        pass

        # Returns dictionary.
        return stock_dicts


def correlate_data(stock_dict, rain_dict):
    """
    This function a stock dictinary and a rain dictionary and returns a list  made of nested lists made of a stock value
    and a rain value if the rain value and stock value have the same date keys.
    :param stock_dict: (dict) A dictionary with dates as keys and stock changes as values.
    :param rain_dict: (dict) A dicitonary with dates as keys and rainfall as values.
    :return: (list) a list of list of correlating stocks and rainfall values.
    """

    # Sets variable new_list and sub_data_List as empty lists.
    new_list = []
    sub_data_list = []

    # Calls the values of the stock dictionary and the rain dictionary only if the key dates match for each list.
    for key in stock_dict:
        if key in rain_dict:
            stock_data = stock_dict[key]
            rain_data = rain_dict[key]

            # Appends the values with same key dates to sub_data_list and appends the sub list to new_List.
            sub_data_list.append(stock_data)
            sub_data_list.append(rain_data)
            new_list.append(sub_data_list)
            sub_data_list = []

    # Returns the new list.
    return new_list


def scatter_plot(data, format, name, done):
    """
    Takes correlated list data of rainfall and stock data and a list and uses format to color and make symbols in a
    scatter plot graph. It then uses name to label the scatter plot symbol and sets done as true when its finished.
    :param data: (list) a list of correlated rainfall and stock data.
    :param format: (string) a plt format of color and symbol)
    :param name: (string) the name of the color and symbol
    :param done: (bool) True if last plot is plotted
    """
    # Sets variable x_list and y_list as empty lists.
    x_list = []
    y_list = []

    # Creates x and y value lists from the nested lists, setting rainfall values as x and stock values as y.
    for index in range(len(data)):
        x = float(data[index][1])
        y = float(data[index][0])
        x_list.append(x)
        y_list.append(y)

    # Plots the points of format design at each x and y value in the list and labels the point as name.
    plt.plot(x_list, y_list, format, label=name)

    # Sets done equal to true and gives the graph a title and a legend only if done is true.
    done = True
    if done:
        plt.title("Rainfall vs Price change")
        plt.legend()


def main():
    """
    This program will ask the user for: an input of a rainfall data file, an input of a stock data file, and two stock
    symbols. One of them has to be either Microsoft (MSFT) or Amazon (AMZN), both of which are headquartered in Seattle.
    The other symbol has to be another company that does not have an headquarters in Seattle.
    It will then generate a correlated data of data with same dates from the two data files using the correlate_data
    function by first using parse_rainfall and parse_stock to turn the data into a dictionary with date as key and
    either stock change of the chosen company or amount of rainfall as values. The function will finally plot a
    scatter plot graph  using function scatter_plot and will show the graph with the legend.
    """

    # Asks for input of a rainfall data file, a stock data file, a symbol of either MSFT or AMZN, and another symbol.
    rain_file = input("Please enter any rainfall data file")
    stock_file = input("Please enter any stock data file")
    seattle_stock = input("Please enter either Microsoft(MSFT) or Amazon(AMZN) as a stock symbol")
    other_stock = input("Please enter a different stock symbol that is not primarily in Seattle")

    # Runs parse_rainfall on the rainfall file and parse_stock on the stock file with the appropiate symbol.
    rain_dict_data = parse_rainfall(rain_file)
    stock1_dict_data = parse_stock(stock_file, seattle_stock)
    stock2_dict_data = parse_stock(stock_file, other_stock)

    # Runs correlate_data on the rain dictionary with each stock  dictionary from parse_rainfall and parse_stock.
    correlation1 = correlate_data(stock1_dict_data, rain_dict_data)
    correlation2 = correlate_data(stock2_dict_data, rain_dict_data)

    # Runs scatter_plot on each correlated data from correlate_data and shows the final graph.
    scatter_plot(correlation1, "bo", seattle_stock, False)
    scatter_plot(correlation2, "r+", other_stock, True)


if __name__ == "__main__":
    main()
    if len(sys.argv) == 1:
        plt.show()
    else:
        plt.savefig(sys.argv[1])
