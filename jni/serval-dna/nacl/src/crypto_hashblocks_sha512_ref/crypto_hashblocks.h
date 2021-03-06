#ifndef crypto_hashblocks_H
#define crypto_hashblocks_H

#include "crypto_hashblocks_sha512.h"

#define crypto_hashblocks crypto_hashblocks_sha512
/* CHEESEBURGER crypto_hashblocks_sha512 */
#define crypto_hashblocks_STATEBYTES crypto_hashblocks_sha512_STATEBYTES
/* CHEESEBURGER crypto_hashblocks_sha512_STATEBYTES */
#define crypto_hashblocks_BLOCKBYTES crypto_hashblocks_sha512_BLOCKBYTES
/* CHEESEBURGER crypto_hashblocks_sha512_BLOCKBYTES */
#define crypto_hashblocks_PRIMITIVE "sha512"
#define crypto_hashblocks_IMPLEMENTATION crypto_hashblocks_sha512_IMPLEMENTATION
#define crypto_hashblocks_VERSION crypto_hashblocks_sha512_VERSION

#endif
