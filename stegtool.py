from PIL import Image
import random
import sys
from math import log10, log2
import bisect
#The header is a 4 byte integer representing the number of
#bytes/characters in the secret text
HEADER_LENGTH = 4

def get_pixels(image, zigzag=0):
	"""Return a list of pixel values for a greyscale image

	Keyword arguments:
	image -- PIL Image object converted to greyscale(L)
	zigzag -- flag to flatten pixels in zigzag manner"""

	pixel_values = list(image.getdata())
	pixels_itr = 0
	if zigzag == 1:
		pixels_itr = image.width
		while pixels_itr < len(pixel_values):
			pixel_values[pixels_itr : pixels_itr + image.width] \
			= (pixel_values[pixels_itr : pixels_itr + image.width][::-1])
			pixels_itr = pixels_itr + 2 * image.width
	return pixel_values

def put_pixels(image, pixel_values, zigzag=0):
	"""Return an Image after writing pixel values

	Keyword arguments:
	image -- PIL Image object to write into
	pixel_values -- pixel values to be written
	zigzag -- flag to identify if the pixels were flattened in zigzag mannner"""

	if zigzag == 1:
		pixels_itr = image.width
		while pixels_itr < len(pixel_values):
			pixel_values[pixels_itr : pixels_itr + image.width] \
			= (pixel_values[pixels_itr : pixels_itr + image.width][::-1])
			pixels_itr = pixels_itr + 2 * image.width
	image.putdata(pixel_values)
	return image

def get_payload_bytes(secret_text):
	"""Create a payload and return a bytearray

	Keyword arguments:
	secret_text -- The text to be embedded(ascii)

	Create a header containing the length of the text as a
	32 bit big-endian integer and prefix it to a byte string
	of the secret text encoded as ascii	"""

	return (len(secret_text).to_bytes(HEADER_LENGTH, byteorder='big') 
			+ bytes(secret_text, 'ascii'))

def get_permutation(rng, payload_size, image_size):
	"""Return a permutation of indices to permute over the pixels

	Keyword arguments:
	rng -- a random number generator seeded with a password
	payload_size -- the number of elements of the permutation needed
	image_size -- the range of indices to permute over
	
	Performs a Fisher-Yates shuffle of numbers from 1 to image_size
	and returns the first payload_size elements"""
	
	permutation = [i for i in range(image_size+1)]
	
	for i in range(payload_size):
		try:
			rand_ind = rng.randrange(i,image_size+1)
		except ValueError:
			return 0
		permutation[i], permutation[rand_ind] \
		= (permutation[rand_ind], permutation[i])
	#Need only the first payload_size elements
	permutation = permutation[0:payload_size]
	return permutation

def get_psnr(cover_pixels, steg_pixels):
	"""Calculate and return the PSNR

	Keyword arguments:
	cover_pixles -- pixel values of the cover image
	steg_pixels -- pixels values of the steg image"""
	
	image_size = len(cover_pixels)
	mse = 0
	for i in range(image_size):
		mse = mse + ((cover_pixels[i] - steg_pixels[i]) ** 2)
	mse = mse / image_size
	psnr = 10 * log10(255 * 255 / mse)
	return psnr

def get_payload_bits(payload_bytes):
	"""Return a list of bits from a list of bytes

	Keyword arguments:
	payload_bytes -- a list of bytes"""

	payload_bits = list()
	#convert each byte to a sequence of bits
	for byte in payload_bytes:
		temp = list()
		for i in range(8):
			temp.append(byte >> i & 1)
		#temp has the bits in reversed order
		payload_bits.extend(temp[::-1])
	return payload_bits

def lsb_encrypt(pixels, payload_bytes, indices):
	"""Embed the payload in the LSB of the pixels and return the modified image

	Keyword arguments:
	pixels -- the pixels of the cover image
	payload_bytes -- the secret message with the header as a bytearray
	indices -- the indices of the pixels where the message is to be embedded"""

	payload_bits = get_payload_bits(payload_bytes)
	#modify the LSBs of chosen pixels to match the payload bits
	count = 0
	for bit in payload_bits:
		#ind is the index of the pixel value to be mmodified
		ind = indices[count]
		#if the LSB already matches the payload bit, leave it alone!
		if (bit and pixels[ind] % 2 == 0) or (not bit and pixels[ind] % 2 == 1):
			pixels[ind] = pixels[ind] + 1
		count = count + 1
	return pixels

def emd_function_value(pixel_group, base):
	"""Calculate and return the f value of the given pixel group

	f value is defined as a weighted sum of the pixel values
	modulo a chosen base"""

	f_value = 0
	for i in range(len(pixel_group)):
		f_value = (f_value + pixel_group[i] * (i + 1)) % base
	return f_value

def emd_embed_in_group(pixel_group, digit, base):
	"""Embed the digit in the given pixel group and return the pixel group

	The pixel group is modified so that the f value of the modified group
	is equal to the digit we want to embed"""

	f_value = emd_function_value(pixel_group, base)

	#check if the f value is equal to the digit we want to embed
	if digit != f_value:
		#modify an appropriate pixel if they are not equal
		s = (digit - f_value) % base
		if s <= 3:
			if pixel_group[s - 1] < 255:
				pixel_group[s - 1] = pixel_group[s - 1] + 1
			#the maximum value of a pixel is 255
			#in case we need to increase a pixel that has value 255
			#reduce that pixel by 1, and try to embed the digit in the
			#modified pixel group
			else:
				pixel_group[s - 1] = pixel_group[s - 1] - 1
				pixel_group = emd_embed_in_group(pixel_group, digit, base)
		else:
			if pixel_group[6 - s] > 0:
				pixel_group[6 - s] = pixel_group[6 - s] - 1
			#the minimum value of a pixel is 0
			#deal with underflow similar to overflow
			else:
				pixel_group[6 - s] = pixel_group[6 - s] + 1
				pixel_group = emd_embed_in_group(pixel_group, digit, base)
	return pixel_group

def emd_encrypt(pixels, payload_bytes, indices):
	"""Embed the payload by EMD and return the modified image

	Keyword arguments:
	pixels -- the pixels of the cover image
	payload_bytes -- the secret message with the header as a bytearray
	indices -- the indices of the pixels where the message is to be embedded"""

	payload_digits = list()
	#In the EMD method, a sequence of bits are grouped into 
	#smaller groups of 'l' bits. Each of these groups, taken as
	#a decimal number, is then converted to a group of 'k' digits
	#in a (2n+1)-ary notational system(base). Each such digit
	#is embedded in a group on n pixels. The parameters are related as
	# l = floor(k * log2(2n + 1)). l is chosen as 8 here
	k = 3
	n = 3
	base = 7
	#Transform the payload from the supplied format to the required format.
	#The first HEADER_LENGTH bytes represent the length of the secret.
	#These need a block k * HEADER_LENGTH digits
	#Retrieve the header from the payload
	message_length = int.from_bytes(payload_bytes[0:HEADER_LENGTH], 
									byteorder='big')
	message_length_digits = list()
	#Convert the messsage length to the required base
	while message_length > 0:
		message_length_digits.append(int(message_length) % base)
		message_length = int(message_length / base)
	#Pad with zeros to get the header length to the required size
	while len(message_length_digits) < (k * HEADER_LENGTH):
		message_length_digits.append(0)
	#Add the header to the payload
	payload_digits.extend(message_length_digits[::-1])
	#Similarly convert each character to the required base
	#Pad with zeros such that each byte is represented by k digits
	for byte in payload_bytes[HEADER_LENGTH :]:
		character_digits = list()
		for i in range(k):
			character_digits.append( int( byte / ( base**i ) ) % base )
		payload_digits.extend(character_digits[::-1])
	#Each digit in the payload is embedded into a group of n pixels
	for i in range(0, n * len(payload_digits), n):
		current_pixel_group = [pixels[j] for j in indices[i:i+n]]
		current_pixel_group = emd_embed_in_group(current_pixel_group, 
										payload_digits[int(i / n)], base)
		#Reflect the changes in the image pixels list
		for j in range(n):
			pixels[indices[i+j]] = current_pixel_group[j]

	return pixels

def de_digits_for_type(maxvalue, base):
	"""Find the max no of digits needed to represent a value in a given base

	Keyword arguments:
	maxvalue -- the maximum decimal value possible for the data type
	base -- the base to which the values would be converted"""
	
	digits = 0
	while maxvalue > 0:
		digits = digits + 1
		maxvalue = int(maxvalue / base)
	return digits

def de_encrypt(pixels, payload_bytes, indices):
	"""Embed the payload by Diamond Encoding and return the modified image

	Keyword arguments:
	pixels -- the pixels of the cover image
	payload_bytes -- the secret message with the header as a bytearray
	indices -- the indices of the pixels where the message is to be embedded"""

	#In the Diamond Encoding method, the secret is represented
	#as a sequence of digits of base 2k^2 + 2k + 1.
	#k is a parameter used in the embedding algorithm. Here k
	#is chosen to be 2.
	k = 2
	base = 2 * k * (k + 1) + 1

	#The first HEADER_LENGTH bytes represent an integer with value
	#upto 2^(8 * HEADER_LENGTH - 1), and the other bytes can have value upto
	#127.The number of base l digits needed depends on these values
	header_maxvalue = 2**(8 * HEADER_LENGTH - 1)
	char_maxvalue = 127
	header_digits = de_digits_for_type(header_maxvalue, base)
	digits_per_character = de_digits_for_type(char_maxvalue, base)
	
	payload_digits = list()

	#Retrieve the header from the payload
	message_length = int.from_bytes(payload_bytes[0:HEADER_LENGTH], 
									byteorder='big')
	message_length_digits = list()
	#Convert the header to a sequence of digits in the required base
	#The final header length is calculated in header_digits, 
	#based on the maximum value it can take
	while message_length > 0:
		message_length_digits.append(int(message_length) % base)
		message_length = int(message_length / base)
	#Pad with zeros to attain the required number of digits
	while len(message_length_digits) < header_digits:
		message_length_digits.append(0)
	#Add the header to the payload
	payload_digits.extend(message_length_digits[::-1])
	#Convert the rest of the payload(the secret characters)
	#into groups of digits in the required base.
	#Each character is assumed to take values upto
	#127 and is represented as groups of digits of length
	#calculated in digits_per_character
	for byte in payload_bytes[HEADER_LENGTH : ]:
		temp = list()
		for i in range(digits_per_character):
			temp.append(int(byte / (base ** i)) % base)
		payload_digits.extend(temp[::-1])

	#Each secret digit is embedded in a block of 2 pixels, 
	#indexed by 2i and 2i+1. The DCV of a pixel block with 
	#pixel values x and y is given by
	#DCV(x, y) = ((2k+1)*x + y) mod base
	#Each pixel group is replaced by another neighbouring pixel group
	#with values close to the original so that the 
	#DCV of the new pixel group matches the secret digit
	#The neighbourhood of a pixel group (x,y) is the set
	#of values (p,q) where |x - p| + |y - q| <= k
	for i in range(len(payload_digits)):
		x = pixels[indices[i]]
		y = pixels[indices[i + 1]]
		s = payload_digits[i]
		
		found_flag = 0
		m = -k
		p = 0
		q = 0
		
		while m in range(-k, k+1) and not found_flag:
			if m <= 0:
				n_list = range(- k - m, k + m + 1)
			else:
				n_list = range(m - k, k - m + 1)
			n = n_list[0]
			while n in n_list and not found_flag:
				p = (x + m)
				q = (y + n)
				if ((2 * k + 1) * p + q) % base == s:
					#The required p and q from the 
					#neighbourhood of (x,y) has been found.
					#In case of overflow or underflow, 
					#add or subtract the base value
					#so that the DCV remains the same.					
					if p > 255:
						p = p - base
					elif p < 0:
						p = p + base
					if q > 255:
						q = q - base
					elif q < 0:
						q = q + base

					pixels[indices[2 * i]] = p 
					pixels[indices[2 * i + 1]] = q

					found_flag = 1
				n = n + 1
			m = m + 1
	return pixels

def pvd_classify(val, bins):
	"""Identify the bin(range) a value belongs to given a list of boundaries

	Keyword arguments:
	val -- the value to be placed in a bin
	bins -- a list containing the bin boundaries"""

	val = abs(val)
	pos = bisect.bisect_right(bins, val)
	lower_bound = bins[pos - 1]
	upper_bound = bins[pos] - 1
	return lower_bound, upper_bound

def pvd_embed_function(pixel_a, pixel_b, diff_val):
	"""Adjust grey values of two pixels to get the desired difference

	Keyword arguments:
	pixel_a, pixel_b -- pixels to be adjusted
	diff_val -- desired difference values"""

	if diff_val < 0:
		if diff_val % 2 == 0:
			floor = int(diff_val / 2)
		else:
			floor = int(diff_val / 2) - 1
	else:
		floor = int(diff_val / 2)
	if diff_val % 2 == 0:
		ceil = floor
	else:
		ceil = floor + 1
	pix_diff = pixel_b - pixel_a
	if pix_diff % 2 == 0:
		pixel_a = pixel_a - floor
		pixel_b = pixel_b + ceil
	else:
		pixel_a = pixel_a - ceil
		pixel_b = pixel_b + floor
	return pixel_a, pixel_b 

def pvd_find_block(pixels, indices, indices_itr):
	"""Find a suitable pixel block to embed bits

	Keyword arguments:
	pixels -- list of pixels
	indices -- list of indices generated by RNG
	indices_itr -- iterator over indices"""

	#The embed function may cause overflow or underflow which is
	#dealt by this function by discarding blocks that result
	#in overflow or underflow
	bins = list((0,2,4,8,12,16,24,32,48,64,96,128,192,256))
	grey_val_a, grey_val_b = -1, -1
	while (grey_val_a < 0 or grey_val_a > 255 or 
			grey_val_b < 0 or grey_val_b > 255):
		index = indices[indices_itr]
		pixel_a = pixels[2 * index]
		pixel_b = pixels[2 * index + 1]
		diff = (pixel_b - pixel_a)
		lower_bound, upper_bound = pvd_classify(diff, bins)
		test_m = upper_bound - diff
		grey_val_a, grey_val_b = pvd_embed_function(pixel_a, pixel_b, test_m)
		indices_itr = indices_itr + 1

	return lower_bound, upper_bound, indices_itr

def pvd_encrypt(pixels, payload_bytes, indices):
	"""Embed the payload by Pixel-value Differencing and return the modified image

	Keyword arguments:
	pixels -- the pixels of the cover image
	payload_bytes -- the secret message with the header as a bytearray
	indices -- the indices of the pixels where the message is to be embedded"""

	payload_bits = get_payload_bits(payload_bytes)
	payload_bits_itr = 0
	indices_itr = 0
	while payload_bits_itr < len(payload_bits):
		#Find a block to embed next set of bits
		lower_bound, upper_bound, indices_itr = pvd_find_block(pixels, 
														indices, indices_itr)
		#Calculate the capacity of the block
		num_bits = int(log2(upper_bound - lower_bound + 1))
		index = indices[indices_itr]
		diff = (pixels[2 * index + 1] - pixels[2 * index])
		embed_value = 0
		#Extract the next set of bits to obtain a number
		while num_bits > 0:
			embed_value = embed_value * 2 + payload_bits[payload_bits_itr]
			num_bits = num_bits - 1
			payload_bits_itr = payload_bits_itr + 1
		#Adjust the pixel block to embed the required value
		new_diff = lower_bound + embed_value
		if diff < 0:
			new_diff = -1 * new_diff
		diff_val = new_diff - diff
		pixels[2 * index], pixels[2 * index + 1] \
		= (pvd_embed_function(pixels[2 * index], pixels[2 * index + 1], diff))
		indices_itr = indices_itr + 1
	return pixels

def encrypt(cover_image, secret_text, encrypt_method, password, destination):
	"""Prepare and encrypt the secret in the cover image and save it

	Keyword arguments:
	cover_image -- PIL Image where the secret is to be embedded
	secret_text -- ascii string of text
	encrypt_method -- either LSB or EMD
	password -- a password for encryption

	Get pixel data from the image and prepare a payload with 
	a header containing the number of bytes in the secret message
	Embed the secret in the cover image using the specified method and save it

	Fail if:
	-- the cover image size is inefficient
	-- the final image cannot be saved"""
	
	pixels = get_pixels(cover_image, (encrypt_method == 'pvd'))
	image_size = len(pixels)
	payload_bytes = get_payload_bytes(secret_text)
	payload_size = 0
	capacity = 0
	#Estimate the number of pixels needed to encrypt
	#the secret for each method.
	if encrypt_method == 'lsb':
		payload_size = 8 * len(payload_bytes)
		capacity = image_size
	elif encrypt_method == 'emd':
		k = 3
		n = 3
		payload_size = k * n * len(payload_bytes)
		capacity = image_size
	elif encrypt_method == 'de':
		k = 2
		base = 2 * k * (k + 1) + 1
		#the first HEADER_LENGTH bytes represent an integer with value
		#upto 2^(8 * HEADER_LENGTH - 1), and the other bytes can have value upto
		#127.
		header_maxvalue = 2**(8 * HEADER_LENGTH - 1)
		char_maxvalue = 127
		header_digits = de_digits_for_type(header_maxvalue, base)
		digits_per_character = de_digits_for_type(char_maxvalue, base)
		#each digit needs 2 pixels
		payload_size = 2 * (header_digits + 
			digits_per_character * (len(payload_bytes) - HEADER_LENGTH))
		capacity = image_size
	elif encrypt_method == 'pvd':
		#bin sizes are 2, 2, 4, 4, 4, 8, 8, 16, 16, 32, 32, 64, and 64
		bins = list((0,2,4,8,12,16,24,32,48,64,96,128,192,256))
		payload_size = 8 * len(payload_bytes)
		capacity = 0
		pixels_itr = 0
		while capacity < payload_size and pixels_itr < image_size:
			lower_bound, upper_bound = pvd_classify(pixels[pixels_itr + 1] - 
										pixels[pixels_itr], bins)
			capacity = capacity + log2(upper_bound - lower_bound + 1)
			pixels_itr = pixels_itr + 2

	if payload_size > capacity:
		print("The secret is too large for the given image!")
		sys.exit(1)
	else:
		#Use an RNG seeded with the password to generate a random
		#set of pixels where the secret will be embedded.
		random.seed(password)
		if encrypt_method == 'pvd':
			if image_size % 2 == 0:
				image_size = image_size - 1
			indices = get_permutation(random, int(image_size / 2), 
										int(image_size / 2))
		else:
			indices = get_permutation(random, payload_size, image_size)
		if encrypt_method == 'lsb':
			steg_pixels = lsb_encrypt(pixels, payload_bytes, indices)
		elif encrypt_method == 'emd':
			steg_pixels = emd_encrypt(pixels, payload_bytes, indices)
		elif encrypt_method == 'de':
			steg_pixels = de_encrypt(pixels, payload_bytes, indices)
		elif encrypt_method == 'pvd':
			steg_pixels = pvd_encrypt(pixels, payload_bytes, indices)

		pixels = get_pixels(cover_image)
		cover_image = put_pixels(cover_image, steg_pixels, 
						(encrypt_method == 'pvd'))
		if destination[-4:] != ".png":
			destination = destination + ".png"
		try:
			cover_image.save(destination)
		except IOError:
			print("Cannot convert and save!")
			sys.exit(1)
		finally:
			print("Saved as %s" % destination)
			print("PSNR:", get_psnr(pixels, steg_pixels), "dB")
			sys.exit(0)

def lsb_decrypt(pixels, image_size, password):
	"""Retrieve the secret from the LSB of the pixels

	Keyword arguments:
	pixels -- the pixels of the steg image
	image_size -- size of the steg image
	password -- password used for encryption

	Try to obtain the message length from the image
	Proceed with extraction as long as there are no errors.
	Wrong password or method may result in an error or garbage."""
	
	try:
		random.seed(password)
		#Get the indices where the header is stored
		header_indices = get_permutation(random, 8 * HEADER_LENGTH, image_size)
		message_size = 0
		#Compute the header value(message length) from the LSBs
		for i in header_indices:
			message_size = message_size << 1 | (pixels[i] & 1)

		message_size = 8 * (message_size + HEADER_LENGTH)
		random.seed(password)
		#Now retrieve the indices of all the secret bits in the payload
		message_indices = get_permutation(random, message_size, image_size)
		#Discard the header indices
		message_indices = message_indices[8 * HEADER_LENGTH:]

		#Reconstruct the secret from the LSBs
		current_character = 0
		message = ""
		count = 0
		for i in message_indices:
			current_character = current_character << 1 | (pixels[i] & 1)
			count = count + 1
			if count % 8 == 0:
				message = message + chr(current_character)
				current_character = 0
		return message
	except:
		print(("Unable to decrypt:\nYour password may be wrong\n"
				"The method may be different\n"
				"The image may not have any secret"))
		sys.exit(1)

def emd_decrypt(pixels, image_size, password):
	"""Retrieve the secret from the pixels by EMD

	Keyword arguments:
	pixels -- the pixels of the steg image
	image_size -- size of the steg image
	password -- password used for encryption

	Try to obtain the message length from the image
	Proceed with extraction as long as there are no errors.
	Wrong password or method may result in an error or garbage."""

	#Each byte is encoded as k digits, and each digit needs n pixels
	#in a 2n+1-ary notational system(base)
	try:
		n = 3
		k = 3
		base = 7
		random.seed(password)
		#Retrieve the indices where the header is embdedded
		header_indices = get_permutation(random, n * k * HEADER_LENGTH, 
										image_size)
		message_size = 0
		#Compute the message length
		for i in range(0, n * k * HEADER_LENGTH, n):
			curr_pixel_group = [pixels[j] for j in header_indices[i:i+n]]
			message_size = (message_size * base + 
							emd_function_value(curr_pixel_group, base))

		message_size = (message_size + HEADER_LENGTH) * k * n
		random.seed(password)
		#Now retrieve the indices of all the secret pixel groups in the payload
		message_indices = get_permutation(random, message_size, image_size)
		#Discard the header indices
		message_indices = message_indices[(HEADER_LENGTH * k * n):]

		#Reconstruct the sequence of secret digits
		message_digits = list()
		for i in range(0, len(message_indices), n):
			current_pixel_group = [pixels[j] for j in message_indices[i:i+n]]
			message_digits.append(emd_function_value(current_pixel_group, 
																	base))
	
		message = ""
		#Reconstruct the secret message from the secret digits
		for i in range(0, len(message_digits), k):
			current_character = 0
		for j in range(k):
			current_character = current_character * base + message_digits[i+j]
			message = message + chr(current_character)
		return message
	except:
		print(("Unable to decrypt:\nYour password may be wrong\n"
				"The method may be different\n"
				"The image may not have any secret"))
		sys.exit(1)

def de_decrypt(pixels, image_size, password):
	"""Retrieve the secret from the pixels by EMD

	Keyword arguments:
	pixels -- the pixels of the steg image
	image_size -- size of the steg image
	password -- password used for encryption

	Try to obtain the message length from the image.
	Proceed with extraction as long as there are no errors.
	Wrong password or method may result in an error or garbage."""

	try:
		k = 2
		base = 2 * k * (k + 1) + 1
		random.seed(password)
		message_size = 0
		#The first HEADER_LENGTH bytes represent an integer with value
		#upto 2^(8 * HEADER_LENGTH - 1), and the other bytes can have value upto
		#127.
		header_maxvalue = 2**(8 * HEADER_LENGTH - 1)
		char_maxvalue = 127
		#the number of base l digits needed depends on these values
		header_digits = de_digits_for_type(header_maxvalue, base)
		digits_per_character = de_digits_for_type(char_maxvalue, base)
		#Retrieve the header indices
		header_indices = get_permutation(random, 2 * header_digits, image_size)
		#Compute the message length
		for i in range(header_digits):
			x = pixels[header_indices[2 * i]]
			y = pixels[header_indices[2 * i + 1]]
			dcv = ((2 * k + 1) * x + y) % base
			message_size = message_size * base + dcv

		random.seed(password)
		#Now retrieve the indices of all the secret pixel blocks in the payload
		total_size = 2 * (header_digits + message_size * digits_per_character)
		message_indices = get_permutation(random, total_size, image_size)
		#Discard the header indices
		message_indices = message_indices[2*header_digits:]

		message = ""
		#Reconstruct the sequence of secret digits
		message_digits = list()
		for i in range(0, len(message_indices), 2):
			x = pixels[message_indices[i]]
			y = pixels[message_indices[i + 1]]
			dcv = ((2 * k + 1) * x + y) % base
			message_digits.append(dcv)
		#Reconstruct the message from the secret digits
		for i in range(0, len(message_digits), digits_per_character):
			current_character = 0
			for j in range(digits_per_character):
				current_character = (current_character * base 
									+ message_digits[i + j])
			message = message + chr(current_character)
		return message
	except:
		print(("Unable to decrypt:\nYour password may be wrong\n"
				"The method may be different\n"
				"The image may not have any secret"))
		sys.exit(1)

def pvd_recover_bits(pixels, indices, indices_itr, size):
	"""Attempt to extract a set of bits from the given pixels

	Keyword arguments:
	pixels -- the pixels of the steg image
	indices -- the indices generated by the RNG
	indices_itr -- iterator over the indices
	size -- number of bits to be recovered"""

	try:
		bits_recovered = 0
		recovered_bits = list()
		while bits_recovered < size:
			#Find the next block which may contain embedded bits
			lower_bound, upper_bound, indices_itr = pvd_find_block(pixels, 
													indices, indices_itr)
			index = indices[indices_itr]
			diff = pixels[2 * index + 1] - pixels[2 * index]
			if diff >= 0:
				embed_value = diff - lower_bound
			else:
				embed_value = -1 * diff - lower_bound
			temp_list = list()
			num_bits = int(log2(upper_bound - lower_bound + 1))
			#Extract the embedded bits
			while num_bits > 0:
				temp_list.append(embed_value % 2)
				embed_value = int(embed_value / 2)
				num_bits = num_bits - 1
			#temp_list has the bits in reversed order
			recovered_bits.extend(temp_list[::-1])
			bits_recovered = bits_recovered + len(temp_list)
			indices_itr = indices_itr + 1
		return recovered_bits, indices_itr
	except:
		print(("Unable to decrypt:\nYour password may be wrong\n"
				"The method may be different\n"
				"The image may not have any secret"))
		sys.exit(1)

def pvd_decrypt(pixels, image_size, password):
	"""Retrieve the secret from the pixels by EMD

	Keyword arguments:
	pixels -- the pixels of the steg image
	image_size -- size of the steg image
	password -- password used for encryption

	Try to obtain the message length from the image.
	Proceed with extraction as long as there are no errors.
	Wrong password or method may result in an error or garbage."""

	try:
		random.seed(password)
		if image_size % 2 == 0:
			image_size = image_size - 1
		indices = get_permutation(random, int(image_size / 2), 
								int(image_size / 2))
		header_size = 8 * HEADER_LENGTH
		indices_itr = 0
		header_bits, indices_itr = pvd_recover_bits(pixels, indices, 
									indices_itr, header_size)
		message_size = 0
		for bit in header_bits:
			message_size = message_size * 2 + bit
		message_size = message_size * 8
		message = ""
		message_bits, indices_itr = pvd_recover_bits(pixels, indices, 
									indices_itr, message_size)
		message_bits_itr = 0
		while message_bits_itr < len(message_bits):
			current_character = 0
			for byte_itr in range(8):
				current_character = (current_character * 2 + 
								message_bits[message_bits_itr])
				message_bits_itr = message_bits_itr + 1
			message = message + chr(current_character)
		return message
	except:
		print(("Unable to decrypt:\nYour password may be wrong\n"
				"The method may be different\n"
				"The image may not have any secret"))
		sys.exit(1)		

def decrypt(steg_image, decrypt_method, password):
	"""Extract the secret message from the steg image

	Keyword arguments:
	steg_image -- PIL Image with the embedded secret
	decrypt_method -- either LSB or EMD
	password -- the password used for encryption"""
	
	pixels = get_pixels(steg_image, (decrypt_method == 'pvd'))
	image_size = len(pixels)
	if decrypt_method == 'lsb':
		message = lsb_decrypt(pixels, image_size, password)
	elif decrypt_method == 'emd':
		message = emd_decrypt(pixels, image_size, password)
	elif decrypt_method == 'de':
		message = de_decrypt(pixels, image_size, password)
	elif decrypt_method == 'pvd':
		message = pvd_decrypt(pixels, image_size, password)
	print("The message is: %s" % message)
	sys.exit(0)

def main():
	"""Get all necessary input and validate

	Prompt the user for the image file name (cover/steg),
	secret text file(for encryption) and a password.
	Fail if:
	-The image file given cannot be opened
	-The text file given cannot be opened
	-The text file given is not text only
	-The text file given cannot be read in ascii"""
	
	image_filename = input("Enter the image file name: ").rstrip()
	try:
		img = Image.open(image_filename).convert("L")
	except OSError:
		print("Cannot open %s" % image_filename)
		sys.exit(1)

	mode = 0
	method = 0
	method_list = list(('lsb', 'emd', 'de', 'pvd'))
	
	while mode != 'e' and mode != 'd':
		mode = input("Do you want to encrypt(e) or decrypt(d)?: ").rstrip()
		if mode != 'e' and mode != 'd':
			print("Invalid option!")
	
	if mode == 'e':
		plaintext_filename = input("Enter the secret"
							"text file name: ").rstrip()
		
		try:
			plaintext_file = open(plaintext_filename, mode='r', 
					encoding='ascii', errors='strict')
		except OSError:
			print("Cannot open %s" % plaintext_filename)
			sys.exit(1)
		except ValueError:
			print("Please give a text-only file(ascii)")
			sys.exit(1)
		
		plaintext = plaintext_file.read()
		plaintext_file.close()
		
		while method not in method_list:
			method = input("Enter the encrytion method\n"
				"- LSB Substitution(lsb)\n"
				"- Exploiting Modification Direction(emd)\n"
				"- Diamond Encoding(de)\n"
				"- Pixel-Value Differncing(pvd)\n").rstrip()
			if method not in method_list:
				print("Invalid method!")
		dest_filename = input("Enter the name of the"
						"destination file: ").rstrip()
		password = input("Enter a password: ").rstrip()
		encrypt(img, plaintext, method, password, dest_filename)

	elif mode == 'd':
		while method not in method_list:
			method = input("Enter the decrytion method\n"
				"- LSB Substitution(lsb)\n"
				"- Exploiting Modification Direction(emd)\n"
				"- Diamond Encoding(de)\n"
				"- Pixel-Value Differncing(pvd)\n").rstrip()
			if method not in method_list:
				print("Invalid method!")

		password = input("Enter a password: ").rstrip()
		decrypt(img, method, password)

if __name__ == '__main__':
	main()