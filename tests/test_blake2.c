/* BLAKE2b and BLAKE2s against vectors generated with Python's hashlib.
 *
 * Every one of the eight named digest lengths is checked, unkeyed, with a
 * one-byte key and with a maximum-length key, over message lengths that
 * straddle both block sizes: empty, a byte either side of 64 and 128, exact
 * multiples, and a few long enough to run the block loop many times.
 *
 * The empty message matters twice over.  Unkeyed it still compresses one
 * block, of zeros, with counter zero; keyed it compresses only the key block,
 * with counter equal to one block.  Those are the two cases a naive
 * implementation gets wrong. */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Hacl.h"

typedef void (*blake2_fn)(uint8_t *out, uint8_t *key, size_t key_len,
                          uint8_t *msg, size_t msg_len);

static int failures = 0;
static uint8_t buf[4096];
static uint8_t keybuf[64];

static void hex(char *dst, const uint8_t *src, size_t n) {
  for (size_t i = 0; i < n; i++)
    sprintf(dst + 2 * i, "%02x", src[i]);
}

/* The message is the first msg_len bytes of a fixed pseudo-random-looking
 * pattern, and the key the first key_len bytes of another; both are generated
 * the same way on the Python side. */
static void check(const char *name, blake2_fn f, size_t digest_len,
                  size_t key_len, size_t msg_len, const char *expected) {
  uint8_t out[64];
  char got[129];

  memset(out, 0, sizeof out);
  f(out, keybuf, key_len, buf, msg_len);
  hex(got, out, digest_len);

  if (strcmp(got, expected) != 0) {
    printf("  FAIL %s\n    got      %s\n    expected %s\n", name, got, expected);
    failures++;
  } else {
    printf("  ok   %s\n", name);
  }
}

int main(void) {
  for (size_t i = 0; i < sizeof buf; i++)
    buf[i] = (uint8_t)((i * 7 + 11) & 0xff);
  for (size_t i = 0; i < sizeof keybuf; i++)
    keybuf[i] = (uint8_t)((i * 3 + 5) & 0xff);

  printf("blake2b_512\n");
  check("blake2b_512 k=0 m=0", Hacl_Hash_Blake2_Named_blake2b_512, 64, 0, 0,
        "786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419d25e1031afee585313896444934eb04b903a685b1448b755d56f701afe9be2ce");
  check("blake2b_512 k=0 m=1", Hacl_Hash_Blake2_Named_blake2b_512, 64, 0, 1,
        "c3fd8f085f18d380c9cafff7213ef009ca6d8b21f87dfbef9d99368be8f58e5e794f20b409cd8f74e573bdbb40f54ca07c5dc498f7de99ddffae43cf033eeebd");
  check("blake2b_512 k=0 m=2", Hacl_Hash_Blake2_Named_blake2b_512, 64, 0, 2,
        "ccdf596e102d3f821ce772c67f22b77340c9125e0ad8d883a1d5aa172a164c7b6f697d6daf6286ae72390d361382b5fd4fadd6a40fb5864a6da1a1fd3a8c8ce9");
  check("blake2b_512 k=0 m=31", Hacl_Hash_Blake2_Named_blake2b_512, 64, 0, 31,
        "db3310c6c89e20b66a6c6375ee2ce36df288126d136290b0fc04d414b4222bca85a9c9353d644b75cf26373f6e0322cbd18eef54d1d7c7f447271e1abe0bf957");
  check("blake2b_512 k=0 m=32", Hacl_Hash_Blake2_Named_blake2b_512, 64, 0, 32,
        "02759983cd2c45492619294878dba9775a7c0d84e2256269947cfe8977c36b15d1238fc6c57669047fdb5fc9b17fc0a694e771947d7c8217825edde343a806ea");
  check("blake2b_512 k=0 m=63", Hacl_Hash_Blake2_Named_blake2b_512, 64, 0, 63,
        "74bcdb2f1cf6df9486f21ce01e57472ec8e4aaa92553bb1fdae068220cd40c6e0a156f6fa699fc7d1f1d0bb85c630d9c0a1e249e651895e638b4bb90574b12ff");
  check("blake2b_512 k=0 m=64", Hacl_Hash_Blake2_Named_blake2b_512, 64, 0, 64,
        "d2b8094acbbbb901f7783698f62498b722a281994b54ddd24970644e84287defd1fc4c73cc3036da1ab63847faca5648cb2ad9c11ab0ad49375cf3b76e3f4373");
  check("blake2b_512 k=0 m=65", Hacl_Hash_Blake2_Named_blake2b_512, 64, 0, 65,
        "f28a357e147d3cf4e23f535e0e34bc9b8d35e7fc43b231023b7a09a822cb596239c8c23d33d68991cefab97d7c8a58c12b9d9a19336bfd56326cc165a7b05d14");
  check("blake2b_512 k=0 m=127", Hacl_Hash_Blake2_Named_blake2b_512, 64, 0, 127,
        "02475e923460186717b477d8924e247468cbd6a9e8a6477fa36cf2ef51097e0bb43bbbe022b2063bd04d4d94c4a1113382cc90c29278c504004d7c563e5a2656");
  check("blake2b_512 k=0 m=128", Hacl_Hash_Blake2_Named_blake2b_512, 64, 0, 128,
        "e1aa6ae49ef23641f916a0b4ddac18e5bdd31c25fe8c143fafa0572189e5f569ea32f62466f9bee41bfd1fd42b3027c109ab529b63c23ac791d3101facb9c5a0");
  check("blake2b_512 k=0 m=129", Hacl_Hash_Blake2_Named_blake2b_512, 64, 0, 129,
        "5d5b550612fed46ef7b0a34bad88ecd64679e1fd64305e07876a46f5ee90455e1f6f6bdc6f1f8bba6941789d57f9f1d9e66e40bc091b3bd777aa7603df55cfd8");
  check("blake2b_512 k=0 m=255", Hacl_Hash_Blake2_Named_blake2b_512, 64, 0, 255,
        "efd62249f85b444dbe97cc7adc536fdad6ad1babb7617fbde2fdfe83be5f82decb03e12efa33ec724bed05ea65ac82d136dd51cad232f9944637de70097e3aa7");
  check("blake2b_512 k=0 m=256", Hacl_Hash_Blake2_Named_blake2b_512, 64, 0, 256,
        "1b69db68eed647d6526f01ca0813c9eccb59837d5fa2f93789cd77696c3a09f19d6de070cdf5003601aba84c531eb5ddad6f90a1974e69905b935b66dc9ff636");
  check("blake2b_512 k=0 m=1000", Hacl_Hash_Blake2_Named_blake2b_512, 64, 0, 1000,
        "c02a2193eef4b7e0f38a4da77425adc473d2e98412d064259b75a9a846e9245cb86dd2e8d46762188cafe9755d822abd6047775104256130a2c3cefaed0107df");
  check("blake2b_512 k=0 m=4096", Hacl_Hash_Blake2_Named_blake2b_512, 64, 0, 4096,
        "aa29d85956bbe9ed2f12e79971683ed0d1c9af4234b0f4a83162f4a4e02bf4dbc3a73b3e5ac39a334ae5c3fba9fd1b5ecbc3946db0d4223fee4ecdeaaa303898");
  check("blake2b_512 k=1 m=0", Hacl_Hash_Blake2_Named_blake2b_512, 64, 1, 0,
        "87181cae936a1efd6ce5530fa77aa5af6baf280ca599fafc0998b9b3021fd179d06575ce456582221acb1fb524958fb32d8786521ea90d622c0e83530175c171");
  check("blake2b_512 k=1 m=1", Hacl_Hash_Blake2_Named_blake2b_512, 64, 1, 1,
        "a550b3c6d2f1bbc244d1c3e1562063d447518ef0f0478783070817fba2b9f5386eb9f4a31a93df9f2854311376f8a304007b2cbdb1d0f8620dd1ac9f4761ce04");
  check("blake2b_512 k=1 m=2", Hacl_Hash_Blake2_Named_blake2b_512, 64, 1, 2,
        "03b710c7be34c03c566fdddf9e06088db46c0702ae3cfe13e11764d39640b55e284f20a78c8f1c7f2cd586b1d1efbae9359050107610bd229be410977a0d9cef");
  check("blake2b_512 k=1 m=31", Hacl_Hash_Blake2_Named_blake2b_512, 64, 1, 31,
        "ac376858e8bf8554e10ab412c9c2c08ed8c5df2fefb5f6bc530cd5b73a588c8629d66c5417cd4951c093c720d43561b5b607b7cde960f6829061f18aa609b100");
  check("blake2b_512 k=1 m=32", Hacl_Hash_Blake2_Named_blake2b_512, 64, 1, 32,
        "f77dd05eb341edfc69203e13ce1e1c613ad92591015b2c52d05755fdb1f0ede2dc5bdd6cd3ef2d16a74e13bdc4333eed277dbfb9b0250ec6f295262807770263");
  check("blake2b_512 k=1 m=63", Hacl_Hash_Blake2_Named_blake2b_512, 64, 1, 63,
        "26c4947ed1e15776c5e0e9f3dac434ae8b59dcbca3a8efe51cb5a530b28a271aaefa05726be927e8aefc1a0bb2c005d55d14634ea7998fe7c9fba2ea758c1360");
  check("blake2b_512 k=1 m=64", Hacl_Hash_Blake2_Named_blake2b_512, 64, 1, 64,
        "9c4773708a4cc75e799fdfc7d0b20fd99329665819be4640902a8c5e9cc4ad1fd9938772a10b08ed31f653e40770ee57b175f965b2e465d51649f00b7944dced");
  check("blake2b_512 k=1 m=65", Hacl_Hash_Blake2_Named_blake2b_512, 64, 1, 65,
        "6de5f308257181a0cbc3ff4d09ec8aefd6049f0dd124684bcd05b4ea28b4536afb6d1883d48537f4e3ad646be1a53f26c3b6832077521dac05c64f171adf07a3");
  check("blake2b_512 k=1 m=127", Hacl_Hash_Blake2_Named_blake2b_512, 64, 1, 127,
        "a5814de5d0858b3895270f10f2ea6eb2ea06b7f952c5282512969e6b98567509d4d9e986065c6cc70e3287b1780ccfeb0bbaeb14106b13fcc925edffa994fdc9");
  check("blake2b_512 k=1 m=128", Hacl_Hash_Blake2_Named_blake2b_512, 64, 1, 128,
        "bca7969b16c8e2a7c105aace5b50b91280623a546c974d9266cfbb3c47da833a69177460de22b5d3700ee3e91327a478e4968c60c34b0f34e6a87c8e6d7280f2");
  check("blake2b_512 k=1 m=129", Hacl_Hash_Blake2_Named_blake2b_512, 64, 1, 129,
        "396c9c49281d46c0f852849a3dc84845c19da2246241450d6b54a2b4f34bd187c8c972209da60c5f4d6644a44eb58c7d9904968908830a4c49465a98bb280989");
  check("blake2b_512 k=1 m=255", Hacl_Hash_Blake2_Named_blake2b_512, 64, 1, 255,
        "d13ef65ff8ff67cb5c1a17b01248c44f71acbcc5a63958a11a8f231d939112c78f7e201c5532ba6e7ceffb2e32c0562cd9210c064fa39ae3358682a5906f595b");
  check("blake2b_512 k=1 m=256", Hacl_Hash_Blake2_Named_blake2b_512, 64, 1, 256,
        "7a704a23aad306b9d3be2cfc6d302840fdcb81505a1dee50ae74659f7e0d4bf39d93e0cfe73ffb1fff287675692749abf4e912816be68262bdba0af01b3f4e52");
  check("blake2b_512 k=1 m=1000", Hacl_Hash_Blake2_Named_blake2b_512, 64, 1, 1000,
        "173ae7828e6bcfc8c5a46968a7367ba675619ff5d808dd2a494fd69be6ffba6954176af94f04737fa0e4bd3cc57ae876cb13095c50acfb2611ef9308e08e85b8");
  check("blake2b_512 k=1 m=4096", Hacl_Hash_Blake2_Named_blake2b_512, 64, 1, 4096,
        "2be200b471702dce9197ae45d766c563170167dd907e86e013a18774a8148ed2be21cf856fa2266c7b3b30f76c4159b1ae43765288f9f08b180f04906b905b99");
  check("blake2b_512 k=64 m=0", Hacl_Hash_Blake2_Named_blake2b_512, 64, 64, 0,
        "2379e73b53df4d436871aa07e07df400bebe1b61d2265d2660dc7ebfe4ed66de1938cc8600121f33b468cb49f58243105c7f30fd83465305325b74889a42c026");
  check("blake2b_512 k=64 m=1", Hacl_Hash_Blake2_Named_blake2b_512, 64, 64, 1,
        "c0c1a57d41dbbaa97cfb210c0be61289c8426b106ca6fd8de0599abab6281f7ab34dfde19135842803e95b292c49af010f0ea118a5aacab3a0d981a417221ea7");
  check("blake2b_512 k=64 m=2", Hacl_Hash_Blake2_Named_blake2b_512, 64, 64, 2,
        "209e89c7af9331eb680d571f1168537a579c20a81ae6fcf8c0d89674d9a2e0d89b8d4cf8edae428b20a2b96c881a40334bb616df6b194a1fca594f80e6f0a93f");
  check("blake2b_512 k=64 m=31", Hacl_Hash_Blake2_Named_blake2b_512, 64, 64, 31,
        "da0f1963afd7c81fcbee8fcd5db06f60b31cbb37dcb2c28ab031aa773185728806f93467781894ce366c972041c39f71c061be357b3338a31b9cf7ae6b636cd7");
  check("blake2b_512 k=64 m=32", Hacl_Hash_Blake2_Named_blake2b_512, 64, 64, 32,
        "2f24a1300c4263b682875a36f521c02f5ea3a718dd7e46d1c9daee6a7b7c7c3b96bf3382d8f206f4e4ca2bf22b4edf7bc37af6633720ee7732df3080ebea2979");
  check("blake2b_512 k=64 m=63", Hacl_Hash_Blake2_Named_blake2b_512, 64, 64, 63,
        "a903ddc7c632c5379e0ce27b4018d1030da0a7933295f0d22229d96e2bab58cd3e36583c9e8121de2ef3f2906b9b5666975b7bfe174f4efb2a25700be081177e");
  check("blake2b_512 k=64 m=64", Hacl_Hash_Blake2_Named_blake2b_512, 64, 64, 64,
        "47686f0abfe6997b31c2d5f8436c063831322c429fd6ca75cc5d06ac4dd755b2150c5c48f6f59df4a9445a9e3918c959f787103a9ded375350cd4d0d0439c58f");
  check("blake2b_512 k=64 m=65", Hacl_Hash_Blake2_Named_blake2b_512, 64, 64, 65,
        "8ac2473b302e913b00778c9a05dd59211202cb242f945d81afb8a1a30aa5448a02656b43fc291b7003589c63223e9cd16e32342619292202886d2cbd54f5cae8");
  check("blake2b_512 k=64 m=127", Hacl_Hash_Blake2_Named_blake2b_512, 64, 64, 127,
        "f9e936e845ab65fb772643275201dee2451edbaeb24eaf247a39109eba2454bd7170bff1a428c951cf6cfc18a662994283271c26a005444491936511393363bb");
  check("blake2b_512 k=64 m=128", Hacl_Hash_Blake2_Named_blake2b_512, 64, 64, 128,
        "8316805b7935a0f5ab0347efa4de987846187b6205bbb5530a1a73d9c42edbdf8596b95f917a14232aef79d9e96a208c1c55c68db51f4f81138f48a8febf104f");
  check("blake2b_512 k=64 m=129", Hacl_Hash_Blake2_Named_blake2b_512, 64, 64, 129,
        "833c7c5c16f063cb2d3a6c37ae9ae72bef013e923ded708f0a82e72d66225350eb48c832d1a3dd65214776bba92ff1af83c0fce7deb4eca9b8563f501279db0a");
  check("blake2b_512 k=64 m=255", Hacl_Hash_Blake2_Named_blake2b_512, 64, 64, 255,
        "9071d44143c342b25b2d5605392b17432f07e3325a69d0eb03643837e0213565d9c4d6dc71d4c434f316752cbebabdfc024a3fc1bd26d47e1a14bc11ce87532c");
  check("blake2b_512 k=64 m=256", Hacl_Hash_Blake2_Named_blake2b_512, 64, 64, 256,
        "100e2af3739b6c60f8290e58cce149acf7be9bde66fa9785da9fbfb0a661635df497e36f03a315b5c350489ff562c9680eda2189ac3e5083e0cd966de931e1d7");
  check("blake2b_512 k=64 m=1000", Hacl_Hash_Blake2_Named_blake2b_512, 64, 64, 1000,
        "ba18cd6883c926f8b8d5a5faa49f143c1c74c20b7f065d7d95cd55bbc71d12db02b0089c752ce48b7afa10aeec831dc9852e9d684caa662ea05d333de034365a");
  check("blake2b_512 k=64 m=4096", Hacl_Hash_Blake2_Named_blake2b_512, 64, 64, 4096,
        "57ac2851a6e5fe9c8b42a0f0b1c9c862cc8839d693eccf5b2e9da06eda54688142cb03b115c94505364de38928464135f6b598f06ca750735758dce0ef299348");

  printf("blake2b_384\n");
  check("blake2b_384 k=0 m=0", Hacl_Hash_Blake2_Named_blake2b_384, 48, 0, 0,
        "b32811423377f52d7862286ee1a72ee540524380fda1724a6f25d7978c6fd3244a6caf0498812673c5e05ef583825100");
  check("blake2b_384 k=0 m=1", Hacl_Hash_Blake2_Named_blake2b_384, 48, 0, 1,
        "b7fdc42de4ac9753769314cfa1ba96b9b18e828c6cfe9d6ea33c08b78cd189690e33eeb6f686930a4a4c5793f6bc563e");
  check("blake2b_384 k=0 m=2", Hacl_Hash_Blake2_Named_blake2b_384, 48, 0, 2,
        "87ba6b6ddcc481775cfaa21736293d968c1636468680fc9cac1d7d64b73e2fa2400d0b0dc62660962db92b16b8b84de6");
  check("blake2b_384 k=0 m=31", Hacl_Hash_Blake2_Named_blake2b_384, 48, 0, 31,
        "276c70cc8a6f9c65c1fa9ca4314184ec9c52aa30e166e79dfb234fa1e0d38f85aae8c53c7a8e3bec7d3248a4c74d7380");
  check("blake2b_384 k=0 m=32", Hacl_Hash_Blake2_Named_blake2b_384, 48, 0, 32,
        "5d7fe7ad8a1effe207115a35d08b3a3c30a8f33acadd134c24eda359b0e08b27aef8d6be672d5af4c0e32f90141e8e74");
  check("blake2b_384 k=0 m=63", Hacl_Hash_Blake2_Named_blake2b_384, 48, 0, 63,
        "cf3251875112d614dad8fc6d7005475c856cd4e67d4604f5dfc216311eb312e156235f456e6a4e7a4cf072155353bfe2");
  check("blake2b_384 k=0 m=64", Hacl_Hash_Blake2_Named_blake2b_384, 48, 0, 64,
        "357ea3c3c51431344244d38b9047181408cdb1c79c39cdcc2632dfe7d1fda33cfa3692de79bf76848ac02dc7dbdabeef");
  check("blake2b_384 k=0 m=65", Hacl_Hash_Blake2_Named_blake2b_384, 48, 0, 65,
        "28c442da9c92b58291039b32d4c6880c2f46a73d69db087324a4ed4758fafec6a12420fe4ed433b2299eee18d6ac66a2");
  check("blake2b_384 k=0 m=127", Hacl_Hash_Blake2_Named_blake2b_384, 48, 0, 127,
        "e69cc33bc7d7e652a1c27a89ea8dae46f2b9eff772b48e50ba8b10ccdd2baebc44dcc812774f7ab885661d4c7dc3e194");
  check("blake2b_384 k=0 m=128", Hacl_Hash_Blake2_Named_blake2b_384, 48, 0, 128,
        "602b4c9865a348d824027faed223b0bf8d75034f020b83cd2700d44f5d47bf0e6bce597bd11e26d1570809c98d8f97dd");
  check("blake2b_384 k=0 m=129", Hacl_Hash_Blake2_Named_blake2b_384, 48, 0, 129,
        "5964978326e7296bf462905f3a81f5f50e115338716224e02dd26e68ecd403accecc7203146ad5a3367051bec6508278");
  check("blake2b_384 k=0 m=255", Hacl_Hash_Blake2_Named_blake2b_384, 48, 0, 255,
        "f9c0f6a073f53c2c30bae58526c3eff4ae6a60cf63f106d9b70b5047cbc99629079b57172dd0cdc084ae01aa47fc95cb");
  check("blake2b_384 k=0 m=256", Hacl_Hash_Blake2_Named_blake2b_384, 48, 0, 256,
        "283a030aa99f6d93b0d8739dc81b37cc4169dee7d1f16ab2222e26f732dcc90f349ac7c714b0e5ae30755815bd1f4047");
  check("blake2b_384 k=0 m=1000", Hacl_Hash_Blake2_Named_blake2b_384, 48, 0, 1000,
        "4aab2f6695069c434ec3a25a7753d0965f892ab5f68bd761bb13ed745c3f4f9a41435e853404c98fbf256fab34d47207");
  check("blake2b_384 k=0 m=4096", Hacl_Hash_Blake2_Named_blake2b_384, 48, 0, 4096,
        "4620d812004f002c732b1fa01cdfd62fe36f99eea51bda02649d2146752db4d8073fe427f9e6a2372b665b4336caefa6");
  check("blake2b_384 k=1 m=0", Hacl_Hash_Blake2_Named_blake2b_384, 48, 1, 0,
        "0162316841c894358abc21ea655486cbe6a02f3ac35d37335f5eb8d8b723b16572132356e28bc267dc658c7b2de96b77");
  check("blake2b_384 k=1 m=1", Hacl_Hash_Blake2_Named_blake2b_384, 48, 1, 1,
        "4fd1d3e1840e5902ddbefea1e4b125cde8152dfd33fad6a80cf9d455678872a3300675593fbe006b787d1d7e31e8cc57");
  check("blake2b_384 k=1 m=2", Hacl_Hash_Blake2_Named_blake2b_384, 48, 1, 2,
        "db159852e0044a9895d226f408c313521c27f7c80cf36fd8e29154321a450f17c5619a7118b7981e5df7eae7d8ea4d94");
  check("blake2b_384 k=1 m=31", Hacl_Hash_Blake2_Named_blake2b_384, 48, 1, 31,
        "73599cf337c09f82a7ce2c389f2cb6972a0267920b6c69214bf9c69704a83948b9f76a7acc95f703d76833aaf1c3b805");
  check("blake2b_384 k=1 m=32", Hacl_Hash_Blake2_Named_blake2b_384, 48, 1, 32,
        "9a536b052f11732107d758d73b25cd1933c10fcf71f6e6a4e2b68c2189d6c3d68d76c7b445e92e79b67f5c8d6b033685");
  check("blake2b_384 k=1 m=63", Hacl_Hash_Blake2_Named_blake2b_384, 48, 1, 63,
        "c96a606cb8dc6146afa4e2cf22c6831acc725b76d79bb42f50eb8b43a61256cf09b6f6ebfb79d3ad52744ed47e810c11");
  check("blake2b_384 k=1 m=64", Hacl_Hash_Blake2_Named_blake2b_384, 48, 1, 64,
        "0ebce75a9186658ff864c472db8101465c9c02b776ff7b12e1a74830e9bd3b74c775ff21126fc179e880d8e6de91d30e");
  check("blake2b_384 k=1 m=65", Hacl_Hash_Blake2_Named_blake2b_384, 48, 1, 65,
        "6ff232b4f4b85b3bbff78b1ec98b2e2e4d2e0f50be8142fda00627ec656228c438ed32d2f61e2df7d92f44e9af25f2eb");
  check("blake2b_384 k=1 m=127", Hacl_Hash_Blake2_Named_blake2b_384, 48, 1, 127,
        "14f77ff9750ce9b45e3237d2186f95c56116826dcf55544964a1e1bd65c97cfc1465e33032393348f537af0d7cc33e1b");
  check("blake2b_384 k=1 m=128", Hacl_Hash_Blake2_Named_blake2b_384, 48, 1, 128,
        "6d70c26557f4208001f41313748c055798e27a739d5eb9e88d532a6ae441f90301e2b921b5e7f11e9cd32c14ab6084ea");
  check("blake2b_384 k=1 m=129", Hacl_Hash_Blake2_Named_blake2b_384, 48, 1, 129,
        "2b06072232969029110e8f47512a4ed4431c2fc9cef5875221cb33714556c7068242196afb22d0633c7c7289ed312b95");
  check("blake2b_384 k=1 m=255", Hacl_Hash_Blake2_Named_blake2b_384, 48, 1, 255,
        "dca38e37d91f1060725f02cf34f6937c43b227c951acccbd1cc5084b49ce7a9909dfce6f75deee1dbdca282fe509379e");
  check("blake2b_384 k=1 m=256", Hacl_Hash_Blake2_Named_blake2b_384, 48, 1, 256,
        "09cd9ff388b288d7e4d8120e28e2e9ed61c7e7d80c347c93ca2bf443f426301b2dfb7cfa91fb2cf825d6af9df395ff3b");
  check("blake2b_384 k=1 m=1000", Hacl_Hash_Blake2_Named_blake2b_384, 48, 1, 1000,
        "2e620356d0fcfcebc015cda77c8d26eedf445bd76a2435031369e7f8cfef0f5821dd5ad10b8cbe8d63da212747f81635");
  check("blake2b_384 k=1 m=4096", Hacl_Hash_Blake2_Named_blake2b_384, 48, 1, 4096,
        "773e3fe5be20d077aa56f65df23666976cfc88f7cffdef6953befc14d196922648a270d35137bd14acd4132dd7b24e68");
  check("blake2b_384 k=64 m=0", Hacl_Hash_Blake2_Named_blake2b_384, 48, 64, 0,
        "44c44d4e509a5f56e24085aee9178f26c5a0a57c33bdf70cebacc14ba64dfc4131de8d7b577ec0fd916047c699765e37");
  check("blake2b_384 k=64 m=1", Hacl_Hash_Blake2_Named_blake2b_384, 48, 64, 1,
        "3103cb46903d5995544693fb0922f4e2f13c89d76e7c26d3931e7115b83f95501f7b0c81acc0c00f7a692b7cc57e234f");
  check("blake2b_384 k=64 m=2", Hacl_Hash_Blake2_Named_blake2b_384, 48, 64, 2,
        "0ffbbd1d0aeba42de106c6e9da3c5bf761846d5c0bee4f015f6f2633158111897e110dcd8f217f1c2bd532d1c56ea551");
  check("blake2b_384 k=64 m=31", Hacl_Hash_Blake2_Named_blake2b_384, 48, 64, 31,
        "cad7e938b30d32add67c4734dfd0ae572f88ca97d4d5a4bf054d8afc07689cb4f6ca51af311944c1bde721a63cc4134a");
  check("blake2b_384 k=64 m=32", Hacl_Hash_Blake2_Named_blake2b_384, 48, 64, 32,
        "3a79f20001b07ec64b5480ca8867ebd43b0d8fab252a6bb598add09655c9a2a653fb9b64d40fb6b57f88f03d004a2358");
  check("blake2b_384 k=64 m=63", Hacl_Hash_Blake2_Named_blake2b_384, 48, 64, 63,
        "8103e5b37ef5a7d05d9c4eedb64db69f09178c2f36c376302211d9772ad0ad82edd5dd7b0277d3f04747da44f32e27a2");
  check("blake2b_384 k=64 m=64", Hacl_Hash_Blake2_Named_blake2b_384, 48, 64, 64,
        "c1432134194d9878f00195d714ecabae344a246392a02cc28a22948c07e21ef0177405d189955a3e05f51a9f8b26cbc8");
  check("blake2b_384 k=64 m=65", Hacl_Hash_Blake2_Named_blake2b_384, 48, 64, 65,
        "ea9924fd252db0657d5bc85459ad1e3dfb43eeb54f42b98dc3ed925847ef31b6c8e43af0e470f053c1869ea71815951d");
  check("blake2b_384 k=64 m=127", Hacl_Hash_Blake2_Named_blake2b_384, 48, 64, 127,
        "511e74f87aca919f6061f2e4b949c12b57d37fd4234af6bea1de696193b618fe4b28d3bfedfbcb607ffac7d742863ff4");
  check("blake2b_384 k=64 m=128", Hacl_Hash_Blake2_Named_blake2b_384, 48, 64, 128,
        "e8c20adee4e4de532d078d776ab0235186a13ce311a4b4394add7f2b90295b18ef7b47bd63928b0e9a97e337c3b8d1b5");
  check("blake2b_384 k=64 m=129", Hacl_Hash_Blake2_Named_blake2b_384, 48, 64, 129,
        "5e96087bb78179ac0afffcd6441b3807347ef6b07b0dd419d6ce84b48e1fae19a4edfbb85cedc0df78d39a140d399e34");
  check("blake2b_384 k=64 m=255", Hacl_Hash_Blake2_Named_blake2b_384, 48, 64, 255,
        "5415c82f9eb39ef3a4ffcff8afeaa0de1a605683506e1b6a88b5e61407775c85d2d8deec805ad55e4afb90411c400797");
  check("blake2b_384 k=64 m=256", Hacl_Hash_Blake2_Named_blake2b_384, 48, 64, 256,
        "406e3c9318b2e6c7c6383616285be247744bc50822dd9454c6c0bb90c9571213c5355c9924b883c934d33c5ee4c46c63");
  check("blake2b_384 k=64 m=1000", Hacl_Hash_Blake2_Named_blake2b_384, 48, 64, 1000,
        "a55fe5393d961f6f2e050bbf50af5ce556b14c0079781beb4686216a2a68f34ad4b3b2cdd6265c2658efa158337ec596");
  check("blake2b_384 k=64 m=4096", Hacl_Hash_Blake2_Named_blake2b_384, 48, 64, 4096,
        "80982bf9e370af09cee88e68b98cd97ea9204b1dd42c37a4d260dbe491e4c447a7604ed935a702b21b42748ced79dc7a");

  printf("blake2b_256\n");
  check("blake2b_256 k=0 m=0", Hacl_Hash_Blake2_Named_blake2b_256, 32, 0, 0,
        "0e5751c026e543b2e8ab2eb06099daa1d1e5df47778f7787faab45cdf12fe3a8");
  check("blake2b_256 k=0 m=1", Hacl_Hash_Blake2_Named_blake2b_256, 32, 0, 1,
        "44e9e1dfd31e4c8c8e05d6db76912790ae9b2f989463f59f709cdd3df7393675");
  check("blake2b_256 k=0 m=2", Hacl_Hash_Blake2_Named_blake2b_256, 32, 0, 2,
        "4afcee33a85d2eaff6b90d0e6f241366d38cc4355e60e55812a58d217b0457c2");
  check("blake2b_256 k=0 m=31", Hacl_Hash_Blake2_Named_blake2b_256, 32, 0, 31,
        "b80d5cab9228d37f91b2cfe398b733b3bbe9292cf83b064754760c0fb5c32f43");
  check("blake2b_256 k=0 m=32", Hacl_Hash_Blake2_Named_blake2b_256, 32, 0, 32,
        "8aed94a6de512bbf48b873ad45b2a22d049ac6e37fc9c51e0a5a33fe31daeafb");
  check("blake2b_256 k=0 m=63", Hacl_Hash_Blake2_Named_blake2b_256, 32, 0, 63,
        "e9f5274b6af329fb0e2c0b2fc9c27d8d36198639c36d1d52e02213d18a878439");
  check("blake2b_256 k=0 m=64", Hacl_Hash_Blake2_Named_blake2b_256, 32, 0, 64,
        "b1ceaf26f5de8b69a8eb40f49aa174086fcbca6baafb93d72ce7dc3781020297");
  check("blake2b_256 k=0 m=65", Hacl_Hash_Blake2_Named_blake2b_256, 32, 0, 65,
        "86d4da694c73a513c6f47baaa65442b1b60cd4d1a3b653f35b339458c62b0736");
  check("blake2b_256 k=0 m=127", Hacl_Hash_Blake2_Named_blake2b_256, 32, 0, 127,
        "0b3ad886bf7207c12fa1b12ad08e607b2fa898e66fd14e382be28fdd9b2eeabb");
  check("blake2b_256 k=0 m=128", Hacl_Hash_Blake2_Named_blake2b_256, 32, 0, 128,
        "98b8901372480c7e9e2e4f532f3f4e22f6eef4f556ab20bcfdfa23adb6d0b4b4");
  check("blake2b_256 k=0 m=129", Hacl_Hash_Blake2_Named_blake2b_256, 32, 0, 129,
        "009fbad47a9f9f353f7e10b49a79b0350b72f627da1b4987a35bf44596c751bb");
  check("blake2b_256 k=0 m=255", Hacl_Hash_Blake2_Named_blake2b_256, 32, 0, 255,
        "e36d33e1472286e7c86bf28e8e9dd32dd732d91a3f75f779bf943d021f1711a9");
  check("blake2b_256 k=0 m=256", Hacl_Hash_Blake2_Named_blake2b_256, 32, 0, 256,
        "790403b18fd34693d1786921c94bcb3c9ea03a636d77209f70fb18dcd3fb06a6");
  check("blake2b_256 k=0 m=1000", Hacl_Hash_Blake2_Named_blake2b_256, 32, 0, 1000,
        "6b43442308600c88dd6f38be292d80e9b5b19f9d39ebac85604ae516811ab732");
  check("blake2b_256 k=0 m=4096", Hacl_Hash_Blake2_Named_blake2b_256, 32, 0, 4096,
        "928fdcd547c7fd757e7e03eb84116b17b680ca942c154c726b36925707a16304");
  check("blake2b_256 k=1 m=0", Hacl_Hash_Blake2_Named_blake2b_256, 32, 1, 0,
        "d70fd1283b794ea02695c7770cb4c8b1acf31e84e210defebd535e98b0b68554");
  check("blake2b_256 k=1 m=1", Hacl_Hash_Blake2_Named_blake2b_256, 32, 1, 1,
        "90fa82caa71fc3ad1a419347336a99a1be5ad17fc9cc0a970d79f950c8581deb");
  check("blake2b_256 k=1 m=2", Hacl_Hash_Blake2_Named_blake2b_256, 32, 1, 2,
        "2cafce3efc9da6c4c092a90039ee30a6cf830a75545dab191dd524c6992a5c18");
  check("blake2b_256 k=1 m=31", Hacl_Hash_Blake2_Named_blake2b_256, 32, 1, 31,
        "2531ba693eab51960585af55c35963f0684ac57363b6ff24e9511151547d2710");
  check("blake2b_256 k=1 m=32", Hacl_Hash_Blake2_Named_blake2b_256, 32, 1, 32,
        "06a1607660fdec5e3ec74f2573b8f7e624512452349548254c84af9de2cec579");
  check("blake2b_256 k=1 m=63", Hacl_Hash_Blake2_Named_blake2b_256, 32, 1, 63,
        "012cf9ca766f25e3b38c466b6449fe54f118adf19945e927dd91b0389fddee8f");
  check("blake2b_256 k=1 m=64", Hacl_Hash_Blake2_Named_blake2b_256, 32, 1, 64,
        "a10a323c203ba6a3a7f65b658208c2903eba1db310c75cc334005c26cd9bf5bd");
  check("blake2b_256 k=1 m=65", Hacl_Hash_Blake2_Named_blake2b_256, 32, 1, 65,
        "ecc3aa1534b898a0f4e1556253de8959764a53a8f010db3f340dbddd16c45d77");
  check("blake2b_256 k=1 m=127", Hacl_Hash_Blake2_Named_blake2b_256, 32, 1, 127,
        "ac44403ee83affba82c557f5465acae4c9055798c20510bf171eb17602f06c51");
  check("blake2b_256 k=1 m=128", Hacl_Hash_Blake2_Named_blake2b_256, 32, 1, 128,
        "1bd3c3593f6dd5fd443ce9f49186ebdc4a9ab91e8e1354ff6fcc890090c19a68");
  check("blake2b_256 k=1 m=129", Hacl_Hash_Blake2_Named_blake2b_256, 32, 1, 129,
        "8045b9836d8fa297583147fce3652d4541d5edc7193e9a71ffb79de89736bafd");
  check("blake2b_256 k=1 m=255", Hacl_Hash_Blake2_Named_blake2b_256, 32, 1, 255,
        "e022db8c27dcfaf2df0d51d61a646ca251ca35b3adcc82482e43fcab69f3be4e");
  check("blake2b_256 k=1 m=256", Hacl_Hash_Blake2_Named_blake2b_256, 32, 1, 256,
        "5037bec3ee7c73ee6ac3f9340a784920c467db6c2e312bab0c2efa029e98945e");
  check("blake2b_256 k=1 m=1000", Hacl_Hash_Blake2_Named_blake2b_256, 32, 1, 1000,
        "65a2204d6c16547bc744a196ed2cf86d49bc4c4308ac255f15a4f4248e13584c");
  check("blake2b_256 k=1 m=4096", Hacl_Hash_Blake2_Named_blake2b_256, 32, 1, 4096,
        "523cd3c376da726ae3ba25ea6f2efd1ae09963e7f112b3cbf866b7a427b6a43a");
  check("blake2b_256 k=64 m=0", Hacl_Hash_Blake2_Named_blake2b_256, 32, 64, 0,
        "78c8b8c98b7e5d612d17ef77115993ca26396ad4ccc1831a32dae4cef55929a1");
  check("blake2b_256 k=64 m=1", Hacl_Hash_Blake2_Named_blake2b_256, 32, 64, 1,
        "f6610eb6655356022d946c681480ab1c7413a65736bcf0a065268b58ee24a77e");
  check("blake2b_256 k=64 m=2", Hacl_Hash_Blake2_Named_blake2b_256, 32, 64, 2,
        "35bc2a2cf065d889c829cd3c5e84cbd0820069e38e6c063e5894b826053c5af0");
  check("blake2b_256 k=64 m=31", Hacl_Hash_Blake2_Named_blake2b_256, 32, 64, 31,
        "c1d0abc484801dfc81e3b32e05e2d1af89e4449dd877c194d218ceaed8511119");
  check("blake2b_256 k=64 m=32", Hacl_Hash_Blake2_Named_blake2b_256, 32, 64, 32,
        "9c7b0773db144949184e5eb93976caae3eaaa3a875980e3b977d88cca75c789c");
  check("blake2b_256 k=64 m=63", Hacl_Hash_Blake2_Named_blake2b_256, 32, 64, 63,
        "a4e94f4a96b8fd6ff59bb6dc5f8c20249ae95f95575d3df358dbe8128c8e06bf");
  check("blake2b_256 k=64 m=64", Hacl_Hash_Blake2_Named_blake2b_256, 32, 64, 64,
        "11d73cd39e16cbf3ceddbd3917dce4325e36e237b6a1ab01175bd771b2e1407d");
  check("blake2b_256 k=64 m=65", Hacl_Hash_Blake2_Named_blake2b_256, 32, 64, 65,
        "fc46dfcff2c66b7788326c218f76832b19f1f47b22745ace78982938a7125351");
  check("blake2b_256 k=64 m=127", Hacl_Hash_Blake2_Named_blake2b_256, 32, 64, 127,
        "aa9c54f78837f8033eb677cc1b01e345fb58958538b00b1706b640aefc90afc3");
  check("blake2b_256 k=64 m=128", Hacl_Hash_Blake2_Named_blake2b_256, 32, 64, 128,
        "18f2ed01dbd894a623c70eba23ddf01c98f1662e28fc5a11b4d86e9b7e44443c");
  check("blake2b_256 k=64 m=129", Hacl_Hash_Blake2_Named_blake2b_256, 32, 64, 129,
        "17cb12dd769a72fc40ef79a96b7d40724766939b39e6c6e6c7b95a17bcfe2659");
  check("blake2b_256 k=64 m=255", Hacl_Hash_Blake2_Named_blake2b_256, 32, 64, 255,
        "8e3d0502620eeb6b8a065690360b9912b4f13ba1825fe2c3dbe1e356044db492");
  check("blake2b_256 k=64 m=256", Hacl_Hash_Blake2_Named_blake2b_256, 32, 64, 256,
        "e74944425287b9786b911f5f79a2b5bf49ed8b0a621397847add05cd5ac68adb");
  check("blake2b_256 k=64 m=1000", Hacl_Hash_Blake2_Named_blake2b_256, 32, 64, 1000,
        "e58b5b89ed4f050dad878af58f70c1151ed09e5509b92164a5a20eefb272a4c8");
  check("blake2b_256 k=64 m=4096", Hacl_Hash_Blake2_Named_blake2b_256, 32, 64, 4096,
        "744ce918a1c392752189213c658242b3227c8d8d6955675a0e43027901e458d2");

  printf("blake2b_160\n");
  check("blake2b_160 k=0 m=0", Hacl_Hash_Blake2_Named_blake2b_160, 20, 0, 0,
        "3345524abf6bbe1809449224b5972c41790b6cf2");
  check("blake2b_160 k=0 m=1", Hacl_Hash_Blake2_Named_blake2b_160, 20, 0, 1,
        "e9e6db735744170cf274c5a0fb1dae7cefcba2e1");
  check("blake2b_160 k=0 m=2", Hacl_Hash_Blake2_Named_blake2b_160, 20, 0, 2,
        "b810ec55fabceb2fd916cd55951b433b968d6233");
  check("blake2b_160 k=0 m=31", Hacl_Hash_Blake2_Named_blake2b_160, 20, 0, 31,
        "35bf625e37b08a6e0b20e4a0dfd36616f5b57bcc");
  check("blake2b_160 k=0 m=32", Hacl_Hash_Blake2_Named_blake2b_160, 20, 0, 32,
        "0952938885ad66590f7b36d14a31d588d7c0d43b");
  check("blake2b_160 k=0 m=63", Hacl_Hash_Blake2_Named_blake2b_160, 20, 0, 63,
        "af69032b4c6bd0466c362797b9a6c761adeacb62");
  check("blake2b_160 k=0 m=64", Hacl_Hash_Blake2_Named_blake2b_160, 20, 0, 64,
        "06280cb2f1222d94ee4206c543e03a53b2d55268");
  check("blake2b_160 k=0 m=65", Hacl_Hash_Blake2_Named_blake2b_160, 20, 0, 65,
        "d76d39df68177266b152b078dbb0d088f766660f");
  check("blake2b_160 k=0 m=127", Hacl_Hash_Blake2_Named_blake2b_160, 20, 0, 127,
        "bffd3e1959197c08403c034d9295bedc629720ad");
  check("blake2b_160 k=0 m=128", Hacl_Hash_Blake2_Named_blake2b_160, 20, 0, 128,
        "01961faae2b1ab9f48a3ea5ebaf240a03072bb6c");
  check("blake2b_160 k=0 m=129", Hacl_Hash_Blake2_Named_blake2b_160, 20, 0, 129,
        "3103a8a04619d63261d325adc30aec786dc3acac");
  check("blake2b_160 k=0 m=255", Hacl_Hash_Blake2_Named_blake2b_160, 20, 0, 255,
        "78cf0cd8c58604b7f278bafa69d4254c19c30eed");
  check("blake2b_160 k=0 m=256", Hacl_Hash_Blake2_Named_blake2b_160, 20, 0, 256,
        "e6e133031b4d35113bdfb528bec3a2a442ee81e1");
  check("blake2b_160 k=0 m=1000", Hacl_Hash_Blake2_Named_blake2b_160, 20, 0, 1000,
        "dae0acd351bcc07b22802e0e73dd863319970bcf");
  check("blake2b_160 k=0 m=4096", Hacl_Hash_Blake2_Named_blake2b_160, 20, 0, 4096,
        "1171259b7d4eb980579fe333bca84627aa22824b");
  check("blake2b_160 k=1 m=0", Hacl_Hash_Blake2_Named_blake2b_160, 20, 1, 0,
        "bc7f68030a95252d9be2cd3946b27ed8367ee006");
  check("blake2b_160 k=1 m=1", Hacl_Hash_Blake2_Named_blake2b_160, 20, 1, 1,
        "1cd0e9f665d179c214481a2297856448ec8e171a");
  check("blake2b_160 k=1 m=2", Hacl_Hash_Blake2_Named_blake2b_160, 20, 1, 2,
        "2cf1f4965158af9dbb04bfca9b802eb782a41cff");
  check("blake2b_160 k=1 m=31", Hacl_Hash_Blake2_Named_blake2b_160, 20, 1, 31,
        "e6b6c67821b3c7d72707e8d10a8f08c8aa5ee5d6");
  check("blake2b_160 k=1 m=32", Hacl_Hash_Blake2_Named_blake2b_160, 20, 1, 32,
        "58b6ae21989edba4523e2d3f47436f4b1e43c095");
  check("blake2b_160 k=1 m=63", Hacl_Hash_Blake2_Named_blake2b_160, 20, 1, 63,
        "6abaae344245fab8763d639017fc15036d8bdfba");
  check("blake2b_160 k=1 m=64", Hacl_Hash_Blake2_Named_blake2b_160, 20, 1, 64,
        "25a6fc95aab0e7f079f4962dd00c7ef243610400");
  check("blake2b_160 k=1 m=65", Hacl_Hash_Blake2_Named_blake2b_160, 20, 1, 65,
        "317c3f428bc231bf2244170e29eb22fe132e92ec");
  check("blake2b_160 k=1 m=127", Hacl_Hash_Blake2_Named_blake2b_160, 20, 1, 127,
        "b884473eda826680635526940b8efa94ca56e303");
  check("blake2b_160 k=1 m=128", Hacl_Hash_Blake2_Named_blake2b_160, 20, 1, 128,
        "c66f7f38c813deb18f179a5b33cc2dacf0609bcf");
  check("blake2b_160 k=1 m=129", Hacl_Hash_Blake2_Named_blake2b_160, 20, 1, 129,
        "2195ab15db800f2a88c34b7e50fed2b9477baa62");
  check("blake2b_160 k=1 m=255", Hacl_Hash_Blake2_Named_blake2b_160, 20, 1, 255,
        "bb6319a31ccc9db13f47c1bfc2a78614f34bc073");
  check("blake2b_160 k=1 m=256", Hacl_Hash_Blake2_Named_blake2b_160, 20, 1, 256,
        "7d5cfa8c6454a1c35b034ab8007929487738c5d3");
  check("blake2b_160 k=1 m=1000", Hacl_Hash_Blake2_Named_blake2b_160, 20, 1, 1000,
        "2945506ebdd3cd08ffe251dba044b5198bf01ef7");
  check("blake2b_160 k=1 m=4096", Hacl_Hash_Blake2_Named_blake2b_160, 20, 1, 4096,
        "25badd81c5f86bb3e336b5677031609f8b4d9749");
  check("blake2b_160 k=64 m=0", Hacl_Hash_Blake2_Named_blake2b_160, 20, 64, 0,
        "65e889370942216cdd3cc75f20a030d80292dc7c");
  check("blake2b_160 k=64 m=1", Hacl_Hash_Blake2_Named_blake2b_160, 20, 64, 1,
        "fd3bab264c3bb6a3c0eac637fd73db17737c9300");
  check("blake2b_160 k=64 m=2", Hacl_Hash_Blake2_Named_blake2b_160, 20, 64, 2,
        "6068c064781a4c1f7eabd7cc88192a6ad9bfca0b");
  check("blake2b_160 k=64 m=31", Hacl_Hash_Blake2_Named_blake2b_160, 20, 64, 31,
        "03a5921ddef66db5c09f0a7789ed049fba13caa3");
  check("blake2b_160 k=64 m=32", Hacl_Hash_Blake2_Named_blake2b_160, 20, 64, 32,
        "994e6968e1ce75a0f5c51d06a83517c13cb2cd15");
  check("blake2b_160 k=64 m=63", Hacl_Hash_Blake2_Named_blake2b_160, 20, 64, 63,
        "72e5e2a93fac75032d7761fe2d76253e83e632d9");
  check("blake2b_160 k=64 m=64", Hacl_Hash_Blake2_Named_blake2b_160, 20, 64, 64,
        "8230f8caa10613b1c16af31b6f0f7ef88a61dd4f");
  check("blake2b_160 k=64 m=65", Hacl_Hash_Blake2_Named_blake2b_160, 20, 64, 65,
        "8825b91f905e0d7e0498dad3ce13c4e7aa5db6da");
  check("blake2b_160 k=64 m=127", Hacl_Hash_Blake2_Named_blake2b_160, 20, 64, 127,
        "7b7317ca5c5215bf82f2e30849cc513c573fd551");
  check("blake2b_160 k=64 m=128", Hacl_Hash_Blake2_Named_blake2b_160, 20, 64, 128,
        "c04b3f8540d002f4b32b283d0239ebca5e795345");
  check("blake2b_160 k=64 m=129", Hacl_Hash_Blake2_Named_blake2b_160, 20, 64, 129,
        "b0b2932d78efb4f322c875770ec4bc8b0633e6c1");
  check("blake2b_160 k=64 m=255", Hacl_Hash_Blake2_Named_blake2b_160, 20, 64, 255,
        "64cc2144a10aa5f946fc27d1f2dfadae4b719728");
  check("blake2b_160 k=64 m=256", Hacl_Hash_Blake2_Named_blake2b_160, 20, 64, 256,
        "980be54e4136cf3942d16bb2bcccaceeea27aeb1");
  check("blake2b_160 k=64 m=1000", Hacl_Hash_Blake2_Named_blake2b_160, 20, 64, 1000,
        "c114eb5c0235281dd662c1ce20041c24d45be72d");
  check("blake2b_160 k=64 m=4096", Hacl_Hash_Blake2_Named_blake2b_160, 20, 64, 4096,
        "a0ba509206801b3bcb6f3d202627f809d9fd2904");

  printf("blake2s_256\n");
  check("blake2s_256 k=0 m=0", Hacl_Hash_Blake2_Named_blake2s_256, 32, 0, 0,
        "69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9");
  check("blake2s_256 k=0 m=1", Hacl_Hash_Blake2_Named_blake2s_256, 32, 0, 1,
        "b480c25c1e06eea9e9c3e36754715cf0958e4d14b22a8c2a7bc34ebf75208602");
  check("blake2s_256 k=0 m=2", Hacl_Hash_Blake2_Named_blake2s_256, 32, 0, 2,
        "2d4214bb1468117131184f4d2395e00f0fa517969917bf85813853a590efcc68");
  check("blake2s_256 k=0 m=31", Hacl_Hash_Blake2_Named_blake2s_256, 32, 0, 31,
        "632fd86e9c7e23ab098037a0a07afcf80557826f665835ee99c6f3ee38998416");
  check("blake2s_256 k=0 m=32", Hacl_Hash_Blake2_Named_blake2s_256, 32, 0, 32,
        "ff6d6151531fefb38b881ee447dee451a9715fad1e304d2558521c4bb3b68f9c");
  check("blake2s_256 k=0 m=63", Hacl_Hash_Blake2_Named_blake2s_256, 32, 0, 63,
        "9b3be5344b255a7faed41eb2093aa10f62ba6168d8ad848fcc88e2a376708561");
  check("blake2s_256 k=0 m=64", Hacl_Hash_Blake2_Named_blake2s_256, 32, 0, 64,
        "3a588690acdc77ad0dba26e77d650a7299c52cc08c4f73aee671168fc2e65a57");
  check("blake2s_256 k=0 m=65", Hacl_Hash_Blake2_Named_blake2s_256, 32, 0, 65,
        "068755ee1119ab011243989482ec4e43fd9e876589c579d6266d606afe5fd785");
  check("blake2s_256 k=0 m=127", Hacl_Hash_Blake2_Named_blake2s_256, 32, 0, 127,
        "80e0f09406f9cd33bbe42c62eab741682703b33ce51964ab0195299fd60e693f");
  check("blake2s_256 k=0 m=128", Hacl_Hash_Blake2_Named_blake2s_256, 32, 0, 128,
        "97f69df7ec4c5dd4c439bb23fef627538f56fab6bac81d7346fd903571658d12");
  check("blake2s_256 k=0 m=129", Hacl_Hash_Blake2_Named_blake2s_256, 32, 0, 129,
        "5d81350814cb4c05fa5e002a7e367b20a6debbc6924748065ff216797a863e73");
  check("blake2s_256 k=0 m=255", Hacl_Hash_Blake2_Named_blake2s_256, 32, 0, 255,
        "c1c436f886e41c0aee766592596912e58103f6d19a6afabd47f1b3ef41e12506");
  check("blake2s_256 k=0 m=256", Hacl_Hash_Blake2_Named_blake2s_256, 32, 0, 256,
        "a3d9c837eb12dc6ec0f9ca13774d83a0e0c0de0373d80d10c6450ffc5e12ca33");
  check("blake2s_256 k=0 m=1000", Hacl_Hash_Blake2_Named_blake2s_256, 32, 0, 1000,
        "99f2c5dc758751d0d1bd07309a2d7a97f1bd3dea153fb7daa07476a45e87e3c8");
  check("blake2s_256 k=0 m=4096", Hacl_Hash_Blake2_Named_blake2s_256, 32, 0, 4096,
        "35d17d965c63db61f3511ab4620015e7e6fe19e64d6d30a3eddc20a0d3779719");
  check("blake2s_256 k=1 m=0", Hacl_Hash_Blake2_Named_blake2s_256, 32, 1, 0,
        "867954c29c2838dd775b6d3645e41909ac599afc4dde379a2c9c3c7bf8ea4a25");
  check("blake2s_256 k=1 m=1", Hacl_Hash_Blake2_Named_blake2s_256, 32, 1, 1,
        "69e182ac437a1ed4c55b636bbf61a4a7fe28782631d88b977f125d2715db133b");
  check("blake2s_256 k=1 m=2", Hacl_Hash_Blake2_Named_blake2s_256, 32, 1, 2,
        "cdb61b98ca01d6db59e480b142810bd72b872509381612379569eb86ad030974");
  check("blake2s_256 k=1 m=31", Hacl_Hash_Blake2_Named_blake2s_256, 32, 1, 31,
        "3cf924319014b422843a6426fff9a3333aeb6e675059295d5fad7756bc0c3d36");
  check("blake2s_256 k=1 m=32", Hacl_Hash_Blake2_Named_blake2s_256, 32, 1, 32,
        "f27145e02a213d0f13e10f2ba4acfc133f9399c4c161cea99609a79bd36163ce");
  check("blake2s_256 k=1 m=63", Hacl_Hash_Blake2_Named_blake2s_256, 32, 1, 63,
        "0f0c068b11cf1c396400e69b866589b81b5f8ff67c71517726f815001714123b");
  check("blake2s_256 k=1 m=64", Hacl_Hash_Blake2_Named_blake2s_256, 32, 1, 64,
        "21f31290a6d82ae18a4564cd08949b90f0237c4058f9b5fff74145a4d02646a0");
  check("blake2s_256 k=1 m=65", Hacl_Hash_Blake2_Named_blake2s_256, 32, 1, 65,
        "7ef521c6070deac5a771235ee7b82bb8b05d3fc604fa4c927056af50fade36e0");
  check("blake2s_256 k=1 m=127", Hacl_Hash_Blake2_Named_blake2s_256, 32, 1, 127,
        "3d35f0310ea323250040955f1510c561559ae4231fd9d7ef8278d26651bb7696");
  check("blake2s_256 k=1 m=128", Hacl_Hash_Blake2_Named_blake2s_256, 32, 1, 128,
        "1803c0d0fd641d499ca2b8031c4080bd94822fd93296009739dcfed6332cecc7");
  check("blake2s_256 k=1 m=129", Hacl_Hash_Blake2_Named_blake2s_256, 32, 1, 129,
        "c69a2a139248ed9156deaeaaf0620d143bad07f052c43611a30df61de07902fc");
  check("blake2s_256 k=1 m=255", Hacl_Hash_Blake2_Named_blake2s_256, 32, 1, 255,
        "6ad98d8a07f9e38464659f7b87e1e8a57a4c4659cd5dce63c3d1449ca51f302b");
  check("blake2s_256 k=1 m=256", Hacl_Hash_Blake2_Named_blake2s_256, 32, 1, 256,
        "8877632ef79b6d5dc6cb99c01fb12cd5c7f6232d3d9d3d40df240b899e0d9ba0");
  check("blake2s_256 k=1 m=1000", Hacl_Hash_Blake2_Named_blake2s_256, 32, 1, 1000,
        "ab6a492922ee08ce3bddd76f0082865e7063df3cc7f9d6c3b03336c51f6556fa");
  check("blake2s_256 k=1 m=4096", Hacl_Hash_Blake2_Named_blake2s_256, 32, 1, 4096,
        "60ea7c7f73b9bfacd2fa0c2ee7dfa671a1c0f9e1d1a18a1769c574dcc246845c");
  check("blake2s_256 k=32 m=0", Hacl_Hash_Blake2_Named_blake2s_256, 32, 32, 0,
        "dd56ad29f0624bf76ce0bd024487b2606d90060d3e09b4026459fdb6245ba785");
  check("blake2s_256 k=32 m=1", Hacl_Hash_Blake2_Named_blake2s_256, 32, 32, 1,
        "3b392df498cefbb5ff05bfcbc08597ddf9514629b1231fe3f397e14423eff7ef");
  check("blake2s_256 k=32 m=2", Hacl_Hash_Blake2_Named_blake2s_256, 32, 32, 2,
        "2be5aae935118f2eacec8adff8f4d2020a4e21e6c5faa87be3d54e193d3678d4");
  check("blake2s_256 k=32 m=31", Hacl_Hash_Blake2_Named_blake2s_256, 32, 32, 31,
        "b66d56a59113ec18bbf8fd03c637be0c7ff52b501bc2c493e349595bbd0679d6");
  check("blake2s_256 k=32 m=32", Hacl_Hash_Blake2_Named_blake2s_256, 32, 32, 32,
        "70c96847f130bd7682063c78fe3c7f5822c9f3a3823a7de1f433706c44c19ad8");
  check("blake2s_256 k=32 m=63", Hacl_Hash_Blake2_Named_blake2s_256, 32, 32, 63,
        "f6a4e5aa4ba0f41637a0d0d32bce83f8eaf8977dbbd5790ca09a49c1165401e5");
  check("blake2s_256 k=32 m=64", Hacl_Hash_Blake2_Named_blake2s_256, 32, 32, 64,
        "76a64ae45a6fffce78b22474e48e0e4b1dc5b5847733f43a055c25054ce3b136");
  check("blake2s_256 k=32 m=65", Hacl_Hash_Blake2_Named_blake2s_256, 32, 32, 65,
        "ffa18166a117ac57aaabf0b89a474238580685fc420519c02838a99d0e6a1ca1");
  check("blake2s_256 k=32 m=127", Hacl_Hash_Blake2_Named_blake2s_256, 32, 32, 127,
        "bd3db98bf2f2483bc1ff73ada3570d238794e32518a3469b5bb04730f6596c9c");
  check("blake2s_256 k=32 m=128", Hacl_Hash_Blake2_Named_blake2s_256, 32, 32, 128,
        "25a6ac69203c7348d8bf2b5199b3282a4bd319e9c45bfba70f78057e8500b8fe");
  check("blake2s_256 k=32 m=129", Hacl_Hash_Blake2_Named_blake2s_256, 32, 32, 129,
        "e5e5cb6607154897534c978fefa84e0f540fc0da91d93e86f566067582989101");
  check("blake2s_256 k=32 m=255", Hacl_Hash_Blake2_Named_blake2s_256, 32, 32, 255,
        "d156164caf0e214e41cda484a145cca167983218028dfb0cc97c1fc5481102ab");
  check("blake2s_256 k=32 m=256", Hacl_Hash_Blake2_Named_blake2s_256, 32, 32, 256,
        "4ce706c5a0d0b22bef0c5af48fdbb6b2ebeaa011ed265b48c7e6ecbde5a4c08a");
  check("blake2s_256 k=32 m=1000", Hacl_Hash_Blake2_Named_blake2s_256, 32, 32, 1000,
        "6b1644ef1cb98498a29334ea97b447a717cd2f2635d4d67a5ac76a6a1920a67e");
  check("blake2s_256 k=32 m=4096", Hacl_Hash_Blake2_Named_blake2s_256, 32, 32, 4096,
        "0ab0de2df031901abdab45ce52b711ceecfb499ab0d0c9768342ff348ce1e4ca");

  printf("blake2s_224\n");
  check("blake2s_224 k=0 m=0", Hacl_Hash_Blake2_Named_blake2s_224, 28, 0, 0,
        "1fa1291e65248b37b3433475b2a0dd63d54a11ecc4e3e034e7bc1ef4");
  check("blake2s_224 k=0 m=1", Hacl_Hash_Blake2_Named_blake2s_224, 28, 0, 1,
        "272fb03cd343a7325124a2ef392f76d53ab53e981f57624cc0f69f60");
  check("blake2s_224 k=0 m=2", Hacl_Hash_Blake2_Named_blake2s_224, 28, 0, 2,
        "a559361795f4ccc2d01e9f1e8ab8e2dd59448cd21daf116e3ed54545");
  check("blake2s_224 k=0 m=31", Hacl_Hash_Blake2_Named_blake2s_224, 28, 0, 31,
        "97996a6f8a91db6818e895bcd38b08f616d6f9fd8622b30b5cd8d94e");
  check("blake2s_224 k=0 m=32", Hacl_Hash_Blake2_Named_blake2s_224, 28, 0, 32,
        "18a676a02817a86556206c02ad093b99d652f1da5f9237b1f03742b1");
  check("blake2s_224 k=0 m=63", Hacl_Hash_Blake2_Named_blake2s_224, 28, 0, 63,
        "01a70dac7c206523393f939735e012d4d956388b24fb31efb431662d");
  check("blake2s_224 k=0 m=64", Hacl_Hash_Blake2_Named_blake2s_224, 28, 0, 64,
        "c207b8b117ed5d74fca3005f71d5cedf3463ded1458fc253eef5594a");
  check("blake2s_224 k=0 m=65", Hacl_Hash_Blake2_Named_blake2s_224, 28, 0, 65,
        "ee980ddf0d2521192c28561cabffc4d4e3d7851dc1b2b897dcbffa59");
  check("blake2s_224 k=0 m=127", Hacl_Hash_Blake2_Named_blake2s_224, 28, 0, 127,
        "d85b944c213c7270d3ad47c2285cdb8d1dd6393a01ed021774d98c3a");
  check("blake2s_224 k=0 m=128", Hacl_Hash_Blake2_Named_blake2s_224, 28, 0, 128,
        "812b61bbe248f4cb92e22e784ad0835a1f5d1e5e909efc72ad8be63f");
  check("blake2s_224 k=0 m=129", Hacl_Hash_Blake2_Named_blake2s_224, 28, 0, 129,
        "321e7a19d8e8d0ca2435561e824c226b2f0c65807bd131f41422d200");
  check("blake2s_224 k=0 m=255", Hacl_Hash_Blake2_Named_blake2s_224, 28, 0, 255,
        "cbe6c1575f5eb2cf2240c8889f0b509f87f245273975531f5c3794fa");
  check("blake2s_224 k=0 m=256", Hacl_Hash_Blake2_Named_blake2s_224, 28, 0, 256,
        "d14983db405654aa8ae4d96476dbb83f3192614ed00a951c861ae5e6");
  check("blake2s_224 k=0 m=1000", Hacl_Hash_Blake2_Named_blake2s_224, 28, 0, 1000,
        "60a738f2ee3fae8c14539bd521b56374863f72480e519eb64337e720");
  check("blake2s_224 k=0 m=4096", Hacl_Hash_Blake2_Named_blake2s_224, 28, 0, 4096,
        "ed9b260f354fff0d7a9628f79eb715205dddf559dbae43ce4d1fafff");
  check("blake2s_224 k=1 m=0", Hacl_Hash_Blake2_Named_blake2s_224, 28, 1, 0,
        "0607666eb7c575ef392c3b8b309fa1356faaaa8116aa83366d5768ed");
  check("blake2s_224 k=1 m=1", Hacl_Hash_Blake2_Named_blake2s_224, 28, 1, 1,
        "93c321c59cedc7939853eb1e3686dd132dcbdc9008c0f3b66d88d36f");
  check("blake2s_224 k=1 m=2", Hacl_Hash_Blake2_Named_blake2s_224, 28, 1, 2,
        "53ec59b5007586317672fd1cfa16ecc65fdbce0be3d8028894dbf516");
  check("blake2s_224 k=1 m=31", Hacl_Hash_Blake2_Named_blake2s_224, 28, 1, 31,
        "db8e5a1c8387593a0ba5a7fa24839ebdb8e80d916deb261de8159c21");
  check("blake2s_224 k=1 m=32", Hacl_Hash_Blake2_Named_blake2s_224, 28, 1, 32,
        "4d223bca97c6e57bcafcc58f638c3500f0aaf4d319a7c58abae27194");
  check("blake2s_224 k=1 m=63", Hacl_Hash_Blake2_Named_blake2s_224, 28, 1, 63,
        "614d3b97154cd0e447f58ee420ef4739256d91440e5ad29c1c2ac4fc");
  check("blake2s_224 k=1 m=64", Hacl_Hash_Blake2_Named_blake2s_224, 28, 1, 64,
        "9d8cf09ba0a62d9ed36af9a0d3d75c2901ceedab59dd388da070c24c");
  check("blake2s_224 k=1 m=65", Hacl_Hash_Blake2_Named_blake2s_224, 28, 1, 65,
        "2774a3c4f3fb0e9bb77249dd30ee4b3785aaf8f9dc22916f541238e0");
  check("blake2s_224 k=1 m=127", Hacl_Hash_Blake2_Named_blake2s_224, 28, 1, 127,
        "9d45e6eac5c44e6c8043458d5b6281a97e6c8cce244d130e5e6d7489");
  check("blake2s_224 k=1 m=128", Hacl_Hash_Blake2_Named_blake2s_224, 28, 1, 128,
        "ac026af0fc5b9d53d173602e7fcff52a321307de3664cfaf603312bd");
  check("blake2s_224 k=1 m=129", Hacl_Hash_Blake2_Named_blake2s_224, 28, 1, 129,
        "98e8934f209705926bb88af81c35f0272784c5dcf6666f958b5882d8");
  check("blake2s_224 k=1 m=255", Hacl_Hash_Blake2_Named_blake2s_224, 28, 1, 255,
        "6fc003d2dc6768edac1e3f2f76d0a9d60a8c1c932dd0f94ce6831cd2");
  check("blake2s_224 k=1 m=256", Hacl_Hash_Blake2_Named_blake2s_224, 28, 1, 256,
        "720eb77e2b8ee4f4c1531f8011403992a4b4960cfe1d8de2c758dbe2");
  check("blake2s_224 k=1 m=1000", Hacl_Hash_Blake2_Named_blake2s_224, 28, 1, 1000,
        "06b7de66c08d5b153016a32d644bf5a830fb240517d548d2afbd4104");
  check("blake2s_224 k=1 m=4096", Hacl_Hash_Blake2_Named_blake2s_224, 28, 1, 4096,
        "fea84ec2d0f5dc4480849440d163c9e6d2e9822494671a90950bfef0");
  check("blake2s_224 k=32 m=0", Hacl_Hash_Blake2_Named_blake2s_224, 28, 32, 0,
        "c5e3699d9867c41078df0560706ef2e28bd0eca214dca565755910b3");
  check("blake2s_224 k=32 m=1", Hacl_Hash_Blake2_Named_blake2s_224, 28, 32, 1,
        "e3086d706443c10ea4325c26f11c63de33237fae34644ad04865ecdc");
  check("blake2s_224 k=32 m=2", Hacl_Hash_Blake2_Named_blake2s_224, 28, 32, 2,
        "d376d3707a482669951f33ee20717a4358142fc1191ba53f6a224200");
  check("blake2s_224 k=32 m=31", Hacl_Hash_Blake2_Named_blake2s_224, 28, 32, 31,
        "595a5680e7b82866d132de7e6e510724495b924e45e3fe92285f1612");
  check("blake2s_224 k=32 m=32", Hacl_Hash_Blake2_Named_blake2s_224, 28, 32, 32,
        "69ba7b9511b309cc51a7780f4a3a63e9d33918bbc45bb81da91c94d9");
  check("blake2s_224 k=32 m=63", Hacl_Hash_Blake2_Named_blake2s_224, 28, 32, 63,
        "7e1c6f35a27efe6cd2597782a4db4b2ec94b4892785bc55118ee8093");
  check("blake2s_224 k=32 m=64", Hacl_Hash_Blake2_Named_blake2s_224, 28, 32, 64,
        "fcc6d2b9284a2a1a77d8c6707f77578134e275082d7db207d44b292f");
  check("blake2s_224 k=32 m=65", Hacl_Hash_Blake2_Named_blake2s_224, 28, 32, 65,
        "f2d3f5b4fa732c567ecea6684068298a2e8a7ec564ea49eb6bae824b");
  check("blake2s_224 k=32 m=127", Hacl_Hash_Blake2_Named_blake2s_224, 28, 32, 127,
        "97675092ee5c439cd0e32742788fd5b03346c5e911be4b9c23fde2c2");
  check("blake2s_224 k=32 m=128", Hacl_Hash_Blake2_Named_blake2s_224, 28, 32, 128,
        "cc2e75faa13672d539eabf2fd454f3d3fda439f1f12a63b13bff8728");
  check("blake2s_224 k=32 m=129", Hacl_Hash_Blake2_Named_blake2s_224, 28, 32, 129,
        "94f492f8d37a99ce7f5bd3432d586c1266b60bb6b3e18be5e42a8256");
  check("blake2s_224 k=32 m=255", Hacl_Hash_Blake2_Named_blake2s_224, 28, 32, 255,
        "e5fc2363a5652cede085183adec918355b3823b95922b1a2cb2e358b");
  check("blake2s_224 k=32 m=256", Hacl_Hash_Blake2_Named_blake2s_224, 28, 32, 256,
        "982e1ecd3425c92a8bd9b823e0fd55ef1b46fc1207718563a33b66e2");
  check("blake2s_224 k=32 m=1000", Hacl_Hash_Blake2_Named_blake2s_224, 28, 32, 1000,
        "2d6453e75bc5ce6b57b8965dd6603c405a79d844a35c5c2187b2f1fb");
  check("blake2s_224 k=32 m=4096", Hacl_Hash_Blake2_Named_blake2s_224, 28, 32, 4096,
        "48d966143127e1f30b358c55938eab6a17bf25585ee5660558b344a0");

  printf("blake2s_160\n");
  check("blake2s_160 k=0 m=0", Hacl_Hash_Blake2_Named_blake2s_160, 20, 0, 0,
        "354c9c33f735962418bdacb9479873429c34916f");
  check("blake2s_160 k=0 m=1", Hacl_Hash_Blake2_Named_blake2s_160, 20, 0, 1,
        "5a98eac1af4bb00a1fefe00014b0b82535c08a6c");
  check("blake2s_160 k=0 m=2", Hacl_Hash_Blake2_Named_blake2s_160, 20, 0, 2,
        "46472c440199e48a7bbe06ce9c6bae382d30e915");
  check("blake2s_160 k=0 m=31", Hacl_Hash_Blake2_Named_blake2s_160, 20, 0, 31,
        "7849d4546f546364de85e27da13a846de4930308");
  check("blake2s_160 k=0 m=32", Hacl_Hash_Blake2_Named_blake2s_160, 20, 0, 32,
        "dd80a6c16f54690f3998a58472157cfdd75d921f");
  check("blake2s_160 k=0 m=63", Hacl_Hash_Blake2_Named_blake2s_160, 20, 0, 63,
        "70c2a37aa6743129a206e59805811726a74ce17d");
  check("blake2s_160 k=0 m=64", Hacl_Hash_Blake2_Named_blake2s_160, 20, 0, 64,
        "453c268e60838748ece20a9193e2473129109026");
  check("blake2s_160 k=0 m=65", Hacl_Hash_Blake2_Named_blake2s_160, 20, 0, 65,
        "bc864e62a1b8e6677e7c7138883d37cdf47c8cbc");
  check("blake2s_160 k=0 m=127", Hacl_Hash_Blake2_Named_blake2s_160, 20, 0, 127,
        "a23fe9717065c76d6af7da4d530d8da3d88db7df");
  check("blake2s_160 k=0 m=128", Hacl_Hash_Blake2_Named_blake2s_160, 20, 0, 128,
        "52c711adb978df1c938c1f96dcb9452636e3d606");
  check("blake2s_160 k=0 m=129", Hacl_Hash_Blake2_Named_blake2s_160, 20, 0, 129,
        "5d36f471170805b68a2c9d682d0861195d100827");
  check("blake2s_160 k=0 m=255", Hacl_Hash_Blake2_Named_blake2s_160, 20, 0, 255,
        "4833db771b58933c5c1e26659192d35f35862e6b");
  check("blake2s_160 k=0 m=256", Hacl_Hash_Blake2_Named_blake2s_160, 20, 0, 256,
        "c6c21915afe5915ac053da72acee1b9b983c99b2");
  check("blake2s_160 k=0 m=1000", Hacl_Hash_Blake2_Named_blake2s_160, 20, 0, 1000,
        "379ed46969782c5f27cc9291f6495a4bc26a0af8");
  check("blake2s_160 k=0 m=4096", Hacl_Hash_Blake2_Named_blake2s_160, 20, 0, 4096,
        "65f7f5c0fc06db774015fc8a6cbdd0eb2713bb25");
  check("blake2s_160 k=1 m=0", Hacl_Hash_Blake2_Named_blake2s_160, 20, 1, 0,
        "9448d7a262f173931044eb2ab5454fff4241a538");
  check("blake2s_160 k=1 m=1", Hacl_Hash_Blake2_Named_blake2s_160, 20, 1, 1,
        "38b15e86b3129556f4d3f8f1d218b3147b0ef2ea");
  check("blake2s_160 k=1 m=2", Hacl_Hash_Blake2_Named_blake2s_160, 20, 1, 2,
        "c17dc3377cafc92c1c66c4ff93803551cd195bf1");
  check("blake2s_160 k=1 m=31", Hacl_Hash_Blake2_Named_blake2s_160, 20, 1, 31,
        "cfeb00b03af283b19b95000cad45383d7a5f8ba5");
  check("blake2s_160 k=1 m=32", Hacl_Hash_Blake2_Named_blake2s_160, 20, 1, 32,
        "9b3f5a22cca0b65502d150c42d5c1ac8e741b09b");
  check("blake2s_160 k=1 m=63", Hacl_Hash_Blake2_Named_blake2s_160, 20, 1, 63,
        "821d178e70976e2ac9e7952265aa4d7d19b2fb65");
  check("blake2s_160 k=1 m=64", Hacl_Hash_Blake2_Named_blake2s_160, 20, 1, 64,
        "13e628f0d8ac0ec00fdda99404e3a7e823b01246");
  check("blake2s_160 k=1 m=65", Hacl_Hash_Blake2_Named_blake2s_160, 20, 1, 65,
        "e655b0ad0fc3c52683f1db53d596c2b801265d65");
  check("blake2s_160 k=1 m=127", Hacl_Hash_Blake2_Named_blake2s_160, 20, 1, 127,
        "a33b5ea744edb71f2658cca82e8804392c0cd4d2");
  check("blake2s_160 k=1 m=128", Hacl_Hash_Blake2_Named_blake2s_160, 20, 1, 128,
        "44f5e54e9e176d6ba80c46b282eaa4d7bd0acaa7");
  check("blake2s_160 k=1 m=129", Hacl_Hash_Blake2_Named_blake2s_160, 20, 1, 129,
        "de42af08b12cc28a63c25d11f53ff36c7432c125");
  check("blake2s_160 k=1 m=255", Hacl_Hash_Blake2_Named_blake2s_160, 20, 1, 255,
        "7b08151dfa375ac2021b25db70e2d33e9b6cbc17");
  check("blake2s_160 k=1 m=256", Hacl_Hash_Blake2_Named_blake2s_160, 20, 1, 256,
        "9a80471e2ac56af42213f291a255707e38b1c504");
  check("blake2s_160 k=1 m=1000", Hacl_Hash_Blake2_Named_blake2s_160, 20, 1, 1000,
        "46adcbef7c7f1f89b154e59c9a72b778a8ebb789");
  check("blake2s_160 k=1 m=4096", Hacl_Hash_Blake2_Named_blake2s_160, 20, 1, 4096,
        "c8e925f0455352d0bcc41502ff703a176d50eb4b");
  check("blake2s_160 k=32 m=0", Hacl_Hash_Blake2_Named_blake2s_160, 20, 32, 0,
        "9fed31bf47036943b66c1c59c47dcfd99ab34289");
  check("blake2s_160 k=32 m=1", Hacl_Hash_Blake2_Named_blake2s_160, 20, 32, 1,
        "5f7baf2f56067e030a51d8de32d325ec21c74c56");
  check("blake2s_160 k=32 m=2", Hacl_Hash_Blake2_Named_blake2s_160, 20, 32, 2,
        "6a6ec20dd91020cd2b67567b4c35127d2ef5ccbe");
  check("blake2s_160 k=32 m=31", Hacl_Hash_Blake2_Named_blake2s_160, 20, 32, 31,
        "ee5c24299749737e1577153b0ebab92a70dd93bd");
  check("blake2s_160 k=32 m=32", Hacl_Hash_Blake2_Named_blake2s_160, 20, 32, 32,
        "2fa30626885e1161e7f640310db720b9dc3bfd20");
  check("blake2s_160 k=32 m=63", Hacl_Hash_Blake2_Named_blake2s_160, 20, 32, 63,
        "0c4b33584481d0044df8b0d638845fdcd10b7065");
  check("blake2s_160 k=32 m=64", Hacl_Hash_Blake2_Named_blake2s_160, 20, 32, 64,
        "ee5e9a18fc6259ca7c20317f17b87ff2032213ec");
  check("blake2s_160 k=32 m=65", Hacl_Hash_Blake2_Named_blake2s_160, 20, 32, 65,
        "e2e32e0984e5ce4bfefa9ffd976957c58b81b954");
  check("blake2s_160 k=32 m=127", Hacl_Hash_Blake2_Named_blake2s_160, 20, 32, 127,
        "effbec397e9cc40644a27b86acf10dce8155dc36");
  check("blake2s_160 k=32 m=128", Hacl_Hash_Blake2_Named_blake2s_160, 20, 32, 128,
        "cc31a592eafab17fa0030fbdb426f034085e8e8b");
  check("blake2s_160 k=32 m=129", Hacl_Hash_Blake2_Named_blake2s_160, 20, 32, 129,
        "0bfb1ee45b506b836a6cc1ae0333740def5c3c58");
  check("blake2s_160 k=32 m=255", Hacl_Hash_Blake2_Named_blake2s_160, 20, 32, 255,
        "0dbb443b13f9ca69f93776854adfe3f67c671d56");
  check("blake2s_160 k=32 m=256", Hacl_Hash_Blake2_Named_blake2s_160, 20, 32, 256,
        "0bcef7f066194b0230e2a6180f7443ceb6282760");
  check("blake2s_160 k=32 m=1000", Hacl_Hash_Blake2_Named_blake2s_160, 20, 32, 1000,
        "0b3a236f6832991f4b85b1ee310a88a8aad89627");
  check("blake2s_160 k=32 m=4096", Hacl_Hash_Blake2_Named_blake2s_160, 20, 32, 4096,
        "a38645c7584fadc1da5a3693a62cba262ede13d6");

  printf("blake2s_128\n");
  check("blake2s_128 k=0 m=0", Hacl_Hash_Blake2_Named_blake2s_128, 16, 0, 0,
        "64550d6ffe2c0a01a14aba1eade0200c");
  check("blake2s_128 k=0 m=1", Hacl_Hash_Blake2_Named_blake2s_128, 16, 0, 1,
        "8d7b89d5c0ff1fb0627835dc36bb4c24");
  check("blake2s_128 k=0 m=2", Hacl_Hash_Blake2_Named_blake2s_128, 16, 0, 2,
        "f86a7b866df2c17a2af92abad1e9baef");
  check("blake2s_128 k=0 m=31", Hacl_Hash_Blake2_Named_blake2s_128, 16, 0, 31,
        "cb961b7200c3c60995623b045bf1aa10");
  check("blake2s_128 k=0 m=32", Hacl_Hash_Blake2_Named_blake2s_128, 16, 0, 32,
        "7f89dbc347c415edd0892935040940f7");
  check("blake2s_128 k=0 m=63", Hacl_Hash_Blake2_Named_blake2s_128, 16, 0, 63,
        "a4d10717f3c85fe5bb36dfd520660cf5");
  check("blake2s_128 k=0 m=64", Hacl_Hash_Blake2_Named_blake2s_128, 16, 0, 64,
        "9da3ce53753693ff11cfdf7eea7c8257");
  check("blake2s_128 k=0 m=65", Hacl_Hash_Blake2_Named_blake2s_128, 16, 0, 65,
        "4c5b6ab9e04bc0b502d58d91ed20f2ef");
  check("blake2s_128 k=0 m=127", Hacl_Hash_Blake2_Named_blake2s_128, 16, 0, 127,
        "6f7cd5be066d976e84993408f36a6c47");
  check("blake2s_128 k=0 m=128", Hacl_Hash_Blake2_Named_blake2s_128, 16, 0, 128,
        "ca7db6dc21695bf85fa5469227c25df1");
  check("blake2s_128 k=0 m=129", Hacl_Hash_Blake2_Named_blake2s_128, 16, 0, 129,
        "96198ec2edab2ebab7dcba6428fad5f4");
  check("blake2s_128 k=0 m=255", Hacl_Hash_Blake2_Named_blake2s_128, 16, 0, 255,
        "6dbe12101f08416d7f5a2587c8aa0d14");
  check("blake2s_128 k=0 m=256", Hacl_Hash_Blake2_Named_blake2s_128, 16, 0, 256,
        "5deb542f97dfb0ae0af12d1ec9823698");
  check("blake2s_128 k=0 m=1000", Hacl_Hash_Blake2_Named_blake2s_128, 16, 0, 1000,
        "80eb3f84dcbebf35cbb94f99ca975c32");
  check("blake2s_128 k=0 m=4096", Hacl_Hash_Blake2_Named_blake2s_128, 16, 0, 4096,
        "3a50a0d58e9d21a28affc6e83b1879de");
  check("blake2s_128 k=1 m=0", Hacl_Hash_Blake2_Named_blake2s_128, 16, 1, 0,
        "4d890a99ff46c0162a98bd3bc93e8bf1");
  check("blake2s_128 k=1 m=1", Hacl_Hash_Blake2_Named_blake2s_128, 16, 1, 1,
        "2ab96fd31613c3609e9ff62695455b51");
  check("blake2s_128 k=1 m=2", Hacl_Hash_Blake2_Named_blake2s_128, 16, 1, 2,
        "1353ffbe5fca3fb533aeaca3edae6fcf");
  check("blake2s_128 k=1 m=31", Hacl_Hash_Blake2_Named_blake2s_128, 16, 1, 31,
        "39087f33017091b69772e1849f77a348");
  check("blake2s_128 k=1 m=32", Hacl_Hash_Blake2_Named_blake2s_128, 16, 1, 32,
        "a6900ad2d9d85cab0275c273de9e9ecd");
  check("blake2s_128 k=1 m=63", Hacl_Hash_Blake2_Named_blake2s_128, 16, 1, 63,
        "18b2cea6442e37df93e4b8df8cf45362");
  check("blake2s_128 k=1 m=64", Hacl_Hash_Blake2_Named_blake2s_128, 16, 1, 64,
        "023fda7536ce4f4c253e3767678f8c29");
  check("blake2s_128 k=1 m=65", Hacl_Hash_Blake2_Named_blake2s_128, 16, 1, 65,
        "ef06c58be62ad6254a01d5ea27efacb1");
  check("blake2s_128 k=1 m=127", Hacl_Hash_Blake2_Named_blake2s_128, 16, 1, 127,
        "c727aac8fd7ba56948ffa4c95ac78817");
  check("blake2s_128 k=1 m=128", Hacl_Hash_Blake2_Named_blake2s_128, 16, 1, 128,
        "6846d60c82c18322f2a1bc92713dc2c1");
  check("blake2s_128 k=1 m=129", Hacl_Hash_Blake2_Named_blake2s_128, 16, 1, 129,
        "d5676485252e7d5494ca07e165402a27");
  check("blake2s_128 k=1 m=255", Hacl_Hash_Blake2_Named_blake2s_128, 16, 1, 255,
        "e6ab875e2bb113dd87367ecb781cb254");
  check("blake2s_128 k=1 m=256", Hacl_Hash_Blake2_Named_blake2s_128, 16, 1, 256,
        "229dab57f067312c5fd32fa79e529e23");
  check("blake2s_128 k=1 m=1000", Hacl_Hash_Blake2_Named_blake2s_128, 16, 1, 1000,
        "2628877a6fc4d524e49b85fd90401608");
  check("blake2s_128 k=1 m=4096", Hacl_Hash_Blake2_Named_blake2s_128, 16, 1, 4096,
        "4ba57a10092f34c7a7ff0ddc93f7442f");
  check("blake2s_128 k=32 m=0", Hacl_Hash_Blake2_Named_blake2s_128, 16, 32, 0,
        "5bb934ab3e1a0f541b5c0ea8c90cfd17");
  check("blake2s_128 k=32 m=1", Hacl_Hash_Blake2_Named_blake2s_128, 16, 32, 1,
        "b1c2612cf4284c4f926c2cc5aa803aa4");
  check("blake2s_128 k=32 m=2", Hacl_Hash_Blake2_Named_blake2s_128, 16, 32, 2,
        "2af6ba2d6f9047e4946a0ca06582a694");
  check("blake2s_128 k=32 m=31", Hacl_Hash_Blake2_Named_blake2s_128, 16, 32, 31,
        "9114cf9b23379c3b765a3a2e3dad9308");
  check("blake2s_128 k=32 m=32", Hacl_Hash_Blake2_Named_blake2s_128, 16, 32, 32,
        "b6cd5fe258dc9c294d3a377edbead220");
  check("blake2s_128 k=32 m=63", Hacl_Hash_Blake2_Named_blake2s_128, 16, 32, 63,
        "8c34b88bce4c9d96701b9d9dcf564212");
  check("blake2s_128 k=32 m=64", Hacl_Hash_Blake2_Named_blake2s_128, 16, 32, 64,
        "205413faba6b6f3aacffe2556d704059");
  check("blake2s_128 k=32 m=65", Hacl_Hash_Blake2_Named_blake2s_128, 16, 32, 65,
        "f7ea494d98d239e582e6b04cdcd4e12b");
  check("blake2s_128 k=32 m=127", Hacl_Hash_Blake2_Named_blake2s_128, 16, 32, 127,
        "0f216c8bd76a523a7cadc7d3662bf2bd");
  check("blake2s_128 k=32 m=128", Hacl_Hash_Blake2_Named_blake2s_128, 16, 32, 128,
        "dca02b3c685b9d71150ea509f1f491c9");
  check("blake2s_128 k=32 m=129", Hacl_Hash_Blake2_Named_blake2s_128, 16, 32, 129,
        "fb20b49df16320a4be5b35cb3632719e");
  check("blake2s_128 k=32 m=255", Hacl_Hash_Blake2_Named_blake2s_128, 16, 32, 255,
        "f42388629b619f10ba4e09cd43c0a4d1");
  check("blake2s_128 k=32 m=256", Hacl_Hash_Blake2_Named_blake2s_128, 16, 32, 256,
        "a847333883ef070c045c851d693a71d2");
  check("blake2s_128 k=32 m=1000", Hacl_Hash_Blake2_Named_blake2s_128, 16, 32, 1000,
        "ace672c18064ff94e56505bc480a959d");
  check("blake2s_128 k=32 m=4096", Hacl_Hash_Blake2_Named_blake2s_128, 16, 32, 4096,
        "ce95a6a25a2db157c74deecfb5dc88cb");

  if (failures) {
    printf("%d failure(s)\n", failures);
    return 1;
  }
  printf("all BLAKE2 vectors pass\n");
  return 0;
}
