def crc16_ibm3740_step(crc_in, data_in):
    """
    Compute CRC16-IBM3740 over 64 bits of data.

    Args:
        crc_in (int): Initial CRC value (16-bit).
        data_in (int): Data input (64-bit).

    Returns:
        int: Computed CRC value (16-bit).
    """
    crc = crc_in
    for k in range(63, -1,-1):
        fb = ((crc >> 15) & 0x1)^ ((data_in >> k) & 0x1)
        crc = ((crc << 1) & 0xFFFE)
        if fb:
            crc ^= 0x1021
    return crc

if __name__ == "__main__":
    # Example inputs
    data_in = 0x000000000032f51a
    crc_in = 0xffff

    # Calculate CRC
    result = crc16_ibm3740_step(crc_in, data_in)

    # Print the result
    print(f"CRC Result: 0x{result:04X}")

    data_in = 0x000000000032f51b
    crc_in = result

    # Calculate CRC
    result = crc16_ibm3740_step(crc_in, data_in)

    # Print the result
    print(f"CRC Result: 0x{result:04X}")