/* The incremental BLAKE2 hashes.
 *
 * The one-shot interface is checked against reference digests in
 * test_blake2.c, so what matters here is that feeding a message in pieces
 * gives the same answer as feeding it whole, whatever the pieces are.  Every
 * one of the eight named lengths is run unkeyed, with a one-byte key and with
 * a maximum-length key, over message lengths that straddle both block sizes,
 * in nine chunk sizes.
 *
 * BLAKE2 buffers between one and block_len bytes rather than between zero and
 * block_len - 1, because its last compression is flagged and so a full buffer
 * may still turn out to be the last block.  The chunk sizes that land exactly
 * on a block boundary -- 64 and 128 -- are therefore the interesting ones, and
 * the empty message is interesting twice over: unkeyed it still compresses one
 * block of zeros at counter zero, keyed it compresses only the key block at
 * counter block_len.
 *
 * We also check the two lifecycle properties the interface promises: digest
 * does not consume the state, so calling it twice gives the same answer and
 * updating after it continues the same message. */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Hacl.h"

static int failures = 0;

static void hex(char *dst, const uint8_t *src, size_t n) {
  for (size_t i = 0; i < n; i++)
    sprintf(dst + 2 * i, "%02x", src[i]);
}

/* One algorithm's three entry points, plus its shapes. */
typedef struct {
  const char *name;
  size_t block_len;
  size_t digest_len;
  size_t key_max;
  void (*init)(void *acc, uint8_t *buf, size_t *tot, uint8_t *key,
               size_t key_len);
  void (*update)(void *acc, uint8_t *buf, size_t *tot, uint8_t *data,
                 size_t data_len);
  void (*digest)(void *acc, uint8_t *buf, size_t *tot, uint8_t *out);
} alg;

/* The generated prototypes take a pointer to uint32_t or to uint64_t for the
 * accumulator; the table below erases that to void * so the eight algorithms
 * fit one shape.  The casts are safe because the pointer representation is the
 * same. */
#define ALG(nm, bl, dl, km, pfx)                                               \
  {                                                                            \
    nm, bl, dl, km,                                                            \
        (void (*)(void *, uint8_t *, size_t *, uint8_t *, size_t))pfx##_init,  \
        (void (*)(void *, uint8_t *, size_t *, uint8_t *, size_t))pfx##_update,\
        (void (*)(void *, uint8_t *, size_t *, uint8_t *))pfx##_digest         \
  }

#define NALG 8
#define NKEY 3
#define NLEN 10

static const alg algs[NALG] = {
    ALG("BLAKE2B-512", 128, 64, 64, Hacl_Streaming_Blake2_blake2b_512),
    ALG("BLAKE2B-384", 128, 48, 64, Hacl_Streaming_Blake2_blake2b_384),
    ALG("BLAKE2B-256", 128, 32, 64, Hacl_Streaming_Blake2_blake2b_256),
    ALG("BLAKE2B-160", 128, 20, 64, Hacl_Streaming_Blake2_blake2b_160),
    ALG("BLAKE2S-256", 64, 32, 32, Hacl_Streaming_Blake2_blake2s_256),
    ALG("BLAKE2S-224", 64, 28, 32, Hacl_Streaming_Blake2_blake2s_224),
    ALG("BLAKE2S-160", 64, 20, 32, Hacl_Streaming_Blake2_blake2s_160),
    ALG("BLAKE2S-128", 64, 16, 32, Hacl_Streaming_Blake2_blake2s_128),
};

static const size_t msg_lens[NLEN] = {0, 1, 63, 64, 65, 127, 128, 129, 256, 1000};
static const size_t chunks[] = {1, 3, 63, 64, 65, 127, 128, 129, 1000};
#define NCHUNKS (sizeof chunks / sizeof chunks[0])

/* expected[alg][key case][message length]; key case 0 is unkeyed, 1 is a
 * one-byte key, 2 is a maximum-length key. */
static const char *const expected[NALG][NKEY][NLEN] = {
    { /* blake2b_512 */
        {
            "786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419d25e1031afee585313896444934eb04b903a685b1448b755d56f701afe9be2ce",
            "c3fd8f085f18d380c9cafff7213ef009ca6d8b21f87dfbef9d99368be8f58e5e794f20b409cd8f74e573bdbb40f54ca07c5dc498f7de99ddffae43cf033eeebd",
            "74bcdb2f1cf6df9486f21ce01e57472ec8e4aaa92553bb1fdae068220cd40c6e0a156f6fa699fc7d1f1d0bb85c630d9c0a1e249e651895e638b4bb90574b12ff",
            "d2b8094acbbbb901f7783698f62498b722a281994b54ddd24970644e84287defd1fc4c73cc3036da1ab63847faca5648cb2ad9c11ab0ad49375cf3b76e3f4373",
            "f28a357e147d3cf4e23f535e0e34bc9b8d35e7fc43b231023b7a09a822cb596239c8c23d33d68991cefab97d7c8a58c12b9d9a19336bfd56326cc165a7b05d14",
            "02475e923460186717b477d8924e247468cbd6a9e8a6477fa36cf2ef51097e0bb43bbbe022b2063bd04d4d94c4a1113382cc90c29278c504004d7c563e5a2656",
            "e1aa6ae49ef23641f916a0b4ddac18e5bdd31c25fe8c143fafa0572189e5f569ea32f62466f9bee41bfd1fd42b3027c109ab529b63c23ac791d3101facb9c5a0",
            "5d5b550612fed46ef7b0a34bad88ecd64679e1fd64305e07876a46f5ee90455e1f6f6bdc6f1f8bba6941789d57f9f1d9e66e40bc091b3bd777aa7603df55cfd8",
            "1b69db68eed647d6526f01ca0813c9eccb59837d5fa2f93789cd77696c3a09f19d6de070cdf5003601aba84c531eb5ddad6f90a1974e69905b935b66dc9ff636",
            "c02a2193eef4b7e0f38a4da77425adc473d2e98412d064259b75a9a846e9245cb86dd2e8d46762188cafe9755d822abd6047775104256130a2c3cefaed0107df",
        },
        {
            "87181cae936a1efd6ce5530fa77aa5af6baf280ca599fafc0998b9b3021fd179d06575ce456582221acb1fb524958fb32d8786521ea90d622c0e83530175c171",
            "a550b3c6d2f1bbc244d1c3e1562063d447518ef0f0478783070817fba2b9f5386eb9f4a31a93df9f2854311376f8a304007b2cbdb1d0f8620dd1ac9f4761ce04",
            "26c4947ed1e15776c5e0e9f3dac434ae8b59dcbca3a8efe51cb5a530b28a271aaefa05726be927e8aefc1a0bb2c005d55d14634ea7998fe7c9fba2ea758c1360",
            "9c4773708a4cc75e799fdfc7d0b20fd99329665819be4640902a8c5e9cc4ad1fd9938772a10b08ed31f653e40770ee57b175f965b2e465d51649f00b7944dced",
            "6de5f308257181a0cbc3ff4d09ec8aefd6049f0dd124684bcd05b4ea28b4536afb6d1883d48537f4e3ad646be1a53f26c3b6832077521dac05c64f171adf07a3",
            "a5814de5d0858b3895270f10f2ea6eb2ea06b7f952c5282512969e6b98567509d4d9e986065c6cc70e3287b1780ccfeb0bbaeb14106b13fcc925edffa994fdc9",
            "bca7969b16c8e2a7c105aace5b50b91280623a546c974d9266cfbb3c47da833a69177460de22b5d3700ee3e91327a478e4968c60c34b0f34e6a87c8e6d7280f2",
            "396c9c49281d46c0f852849a3dc84845c19da2246241450d6b54a2b4f34bd187c8c972209da60c5f4d6644a44eb58c7d9904968908830a4c49465a98bb280989",
            "7a704a23aad306b9d3be2cfc6d302840fdcb81505a1dee50ae74659f7e0d4bf39d93e0cfe73ffb1fff287675692749abf4e912816be68262bdba0af01b3f4e52",
            "173ae7828e6bcfc8c5a46968a7367ba675619ff5d808dd2a494fd69be6ffba6954176af94f04737fa0e4bd3cc57ae876cb13095c50acfb2611ef9308e08e85b8",
        },
        {
            "2379e73b53df4d436871aa07e07df400bebe1b61d2265d2660dc7ebfe4ed66de1938cc8600121f33b468cb49f58243105c7f30fd83465305325b74889a42c026",
            "c0c1a57d41dbbaa97cfb210c0be61289c8426b106ca6fd8de0599abab6281f7ab34dfde19135842803e95b292c49af010f0ea118a5aacab3a0d981a417221ea7",
            "a903ddc7c632c5379e0ce27b4018d1030da0a7933295f0d22229d96e2bab58cd3e36583c9e8121de2ef3f2906b9b5666975b7bfe174f4efb2a25700be081177e",
            "47686f0abfe6997b31c2d5f8436c063831322c429fd6ca75cc5d06ac4dd755b2150c5c48f6f59df4a9445a9e3918c959f787103a9ded375350cd4d0d0439c58f",
            "8ac2473b302e913b00778c9a05dd59211202cb242f945d81afb8a1a30aa5448a02656b43fc291b7003589c63223e9cd16e32342619292202886d2cbd54f5cae8",
            "f9e936e845ab65fb772643275201dee2451edbaeb24eaf247a39109eba2454bd7170bff1a428c951cf6cfc18a662994283271c26a005444491936511393363bb",
            "8316805b7935a0f5ab0347efa4de987846187b6205bbb5530a1a73d9c42edbdf8596b95f917a14232aef79d9e96a208c1c55c68db51f4f81138f48a8febf104f",
            "833c7c5c16f063cb2d3a6c37ae9ae72bef013e923ded708f0a82e72d66225350eb48c832d1a3dd65214776bba92ff1af83c0fce7deb4eca9b8563f501279db0a",
            "100e2af3739b6c60f8290e58cce149acf7be9bde66fa9785da9fbfb0a661635df497e36f03a315b5c350489ff562c9680eda2189ac3e5083e0cd966de931e1d7",
            "ba18cd6883c926f8b8d5a5faa49f143c1c74c20b7f065d7d95cd55bbc71d12db02b0089c752ce48b7afa10aeec831dc9852e9d684caa662ea05d333de034365a",
        },
    },
    { /* blake2b_384 */
        {
            "b32811423377f52d7862286ee1a72ee540524380fda1724a6f25d7978c6fd3244a6caf0498812673c5e05ef583825100",
            "b7fdc42de4ac9753769314cfa1ba96b9b18e828c6cfe9d6ea33c08b78cd189690e33eeb6f686930a4a4c5793f6bc563e",
            "cf3251875112d614dad8fc6d7005475c856cd4e67d4604f5dfc216311eb312e156235f456e6a4e7a4cf072155353bfe2",
            "357ea3c3c51431344244d38b9047181408cdb1c79c39cdcc2632dfe7d1fda33cfa3692de79bf76848ac02dc7dbdabeef",
            "28c442da9c92b58291039b32d4c6880c2f46a73d69db087324a4ed4758fafec6a12420fe4ed433b2299eee18d6ac66a2",
            "e69cc33bc7d7e652a1c27a89ea8dae46f2b9eff772b48e50ba8b10ccdd2baebc44dcc812774f7ab885661d4c7dc3e194",
            "602b4c9865a348d824027faed223b0bf8d75034f020b83cd2700d44f5d47bf0e6bce597bd11e26d1570809c98d8f97dd",
            "5964978326e7296bf462905f3a81f5f50e115338716224e02dd26e68ecd403accecc7203146ad5a3367051bec6508278",
            "283a030aa99f6d93b0d8739dc81b37cc4169dee7d1f16ab2222e26f732dcc90f349ac7c714b0e5ae30755815bd1f4047",
            "4aab2f6695069c434ec3a25a7753d0965f892ab5f68bd761bb13ed745c3f4f9a41435e853404c98fbf256fab34d47207",
        },
        {
            "0162316841c894358abc21ea655486cbe6a02f3ac35d37335f5eb8d8b723b16572132356e28bc267dc658c7b2de96b77",
            "4fd1d3e1840e5902ddbefea1e4b125cde8152dfd33fad6a80cf9d455678872a3300675593fbe006b787d1d7e31e8cc57",
            "c96a606cb8dc6146afa4e2cf22c6831acc725b76d79bb42f50eb8b43a61256cf09b6f6ebfb79d3ad52744ed47e810c11",
            "0ebce75a9186658ff864c472db8101465c9c02b776ff7b12e1a74830e9bd3b74c775ff21126fc179e880d8e6de91d30e",
            "6ff232b4f4b85b3bbff78b1ec98b2e2e4d2e0f50be8142fda00627ec656228c438ed32d2f61e2df7d92f44e9af25f2eb",
            "14f77ff9750ce9b45e3237d2186f95c56116826dcf55544964a1e1bd65c97cfc1465e33032393348f537af0d7cc33e1b",
            "6d70c26557f4208001f41313748c055798e27a739d5eb9e88d532a6ae441f90301e2b921b5e7f11e9cd32c14ab6084ea",
            "2b06072232969029110e8f47512a4ed4431c2fc9cef5875221cb33714556c7068242196afb22d0633c7c7289ed312b95",
            "09cd9ff388b288d7e4d8120e28e2e9ed61c7e7d80c347c93ca2bf443f426301b2dfb7cfa91fb2cf825d6af9df395ff3b",
            "2e620356d0fcfcebc015cda77c8d26eedf445bd76a2435031369e7f8cfef0f5821dd5ad10b8cbe8d63da212747f81635",
        },
        {
            "44c44d4e509a5f56e24085aee9178f26c5a0a57c33bdf70cebacc14ba64dfc4131de8d7b577ec0fd916047c699765e37",
            "3103cb46903d5995544693fb0922f4e2f13c89d76e7c26d3931e7115b83f95501f7b0c81acc0c00f7a692b7cc57e234f",
            "8103e5b37ef5a7d05d9c4eedb64db69f09178c2f36c376302211d9772ad0ad82edd5dd7b0277d3f04747da44f32e27a2",
            "c1432134194d9878f00195d714ecabae344a246392a02cc28a22948c07e21ef0177405d189955a3e05f51a9f8b26cbc8",
            "ea9924fd252db0657d5bc85459ad1e3dfb43eeb54f42b98dc3ed925847ef31b6c8e43af0e470f053c1869ea71815951d",
            "511e74f87aca919f6061f2e4b949c12b57d37fd4234af6bea1de696193b618fe4b28d3bfedfbcb607ffac7d742863ff4",
            "e8c20adee4e4de532d078d776ab0235186a13ce311a4b4394add7f2b90295b18ef7b47bd63928b0e9a97e337c3b8d1b5",
            "5e96087bb78179ac0afffcd6441b3807347ef6b07b0dd419d6ce84b48e1fae19a4edfbb85cedc0df78d39a140d399e34",
            "406e3c9318b2e6c7c6383616285be247744bc50822dd9454c6c0bb90c9571213c5355c9924b883c934d33c5ee4c46c63",
            "a55fe5393d961f6f2e050bbf50af5ce556b14c0079781beb4686216a2a68f34ad4b3b2cdd6265c2658efa158337ec596",
        },
    },
    { /* blake2b_256 */
        {
            "0e5751c026e543b2e8ab2eb06099daa1d1e5df47778f7787faab45cdf12fe3a8",
            "44e9e1dfd31e4c8c8e05d6db76912790ae9b2f989463f59f709cdd3df7393675",
            "e9f5274b6af329fb0e2c0b2fc9c27d8d36198639c36d1d52e02213d18a878439",
            "b1ceaf26f5de8b69a8eb40f49aa174086fcbca6baafb93d72ce7dc3781020297",
            "86d4da694c73a513c6f47baaa65442b1b60cd4d1a3b653f35b339458c62b0736",
            "0b3ad886bf7207c12fa1b12ad08e607b2fa898e66fd14e382be28fdd9b2eeabb",
            "98b8901372480c7e9e2e4f532f3f4e22f6eef4f556ab20bcfdfa23adb6d0b4b4",
            "009fbad47a9f9f353f7e10b49a79b0350b72f627da1b4987a35bf44596c751bb",
            "790403b18fd34693d1786921c94bcb3c9ea03a636d77209f70fb18dcd3fb06a6",
            "6b43442308600c88dd6f38be292d80e9b5b19f9d39ebac85604ae516811ab732",
        },
        {
            "d70fd1283b794ea02695c7770cb4c8b1acf31e84e210defebd535e98b0b68554",
            "90fa82caa71fc3ad1a419347336a99a1be5ad17fc9cc0a970d79f950c8581deb",
            "012cf9ca766f25e3b38c466b6449fe54f118adf19945e927dd91b0389fddee8f",
            "a10a323c203ba6a3a7f65b658208c2903eba1db310c75cc334005c26cd9bf5bd",
            "ecc3aa1534b898a0f4e1556253de8959764a53a8f010db3f340dbddd16c45d77",
            "ac44403ee83affba82c557f5465acae4c9055798c20510bf171eb17602f06c51",
            "1bd3c3593f6dd5fd443ce9f49186ebdc4a9ab91e8e1354ff6fcc890090c19a68",
            "8045b9836d8fa297583147fce3652d4541d5edc7193e9a71ffb79de89736bafd",
            "5037bec3ee7c73ee6ac3f9340a784920c467db6c2e312bab0c2efa029e98945e",
            "65a2204d6c16547bc744a196ed2cf86d49bc4c4308ac255f15a4f4248e13584c",
        },
        {
            "78c8b8c98b7e5d612d17ef77115993ca26396ad4ccc1831a32dae4cef55929a1",
            "f6610eb6655356022d946c681480ab1c7413a65736bcf0a065268b58ee24a77e",
            "a4e94f4a96b8fd6ff59bb6dc5f8c20249ae95f95575d3df358dbe8128c8e06bf",
            "11d73cd39e16cbf3ceddbd3917dce4325e36e237b6a1ab01175bd771b2e1407d",
            "fc46dfcff2c66b7788326c218f76832b19f1f47b22745ace78982938a7125351",
            "aa9c54f78837f8033eb677cc1b01e345fb58958538b00b1706b640aefc90afc3",
            "18f2ed01dbd894a623c70eba23ddf01c98f1662e28fc5a11b4d86e9b7e44443c",
            "17cb12dd769a72fc40ef79a96b7d40724766939b39e6c6e6c7b95a17bcfe2659",
            "e74944425287b9786b911f5f79a2b5bf49ed8b0a621397847add05cd5ac68adb",
            "e58b5b89ed4f050dad878af58f70c1151ed09e5509b92164a5a20eefb272a4c8",
        },
    },
    { /* blake2b_160 */
        {
            "3345524abf6bbe1809449224b5972c41790b6cf2",
            "e9e6db735744170cf274c5a0fb1dae7cefcba2e1",
            "af69032b4c6bd0466c362797b9a6c761adeacb62",
            "06280cb2f1222d94ee4206c543e03a53b2d55268",
            "d76d39df68177266b152b078dbb0d088f766660f",
            "bffd3e1959197c08403c034d9295bedc629720ad",
            "01961faae2b1ab9f48a3ea5ebaf240a03072bb6c",
            "3103a8a04619d63261d325adc30aec786dc3acac",
            "e6e133031b4d35113bdfb528bec3a2a442ee81e1",
            "dae0acd351bcc07b22802e0e73dd863319970bcf",
        },
        {
            "bc7f68030a95252d9be2cd3946b27ed8367ee006",
            "1cd0e9f665d179c214481a2297856448ec8e171a",
            "6abaae344245fab8763d639017fc15036d8bdfba",
            "25a6fc95aab0e7f079f4962dd00c7ef243610400",
            "317c3f428bc231bf2244170e29eb22fe132e92ec",
            "b884473eda826680635526940b8efa94ca56e303",
            "c66f7f38c813deb18f179a5b33cc2dacf0609bcf",
            "2195ab15db800f2a88c34b7e50fed2b9477baa62",
            "7d5cfa8c6454a1c35b034ab8007929487738c5d3",
            "2945506ebdd3cd08ffe251dba044b5198bf01ef7",
        },
        {
            "65e889370942216cdd3cc75f20a030d80292dc7c",
            "fd3bab264c3bb6a3c0eac637fd73db17737c9300",
            "72e5e2a93fac75032d7761fe2d76253e83e632d9",
            "8230f8caa10613b1c16af31b6f0f7ef88a61dd4f",
            "8825b91f905e0d7e0498dad3ce13c4e7aa5db6da",
            "7b7317ca5c5215bf82f2e30849cc513c573fd551",
            "c04b3f8540d002f4b32b283d0239ebca5e795345",
            "b0b2932d78efb4f322c875770ec4bc8b0633e6c1",
            "980be54e4136cf3942d16bb2bcccaceeea27aeb1",
            "c114eb5c0235281dd662c1ce20041c24d45be72d",
        },
    },
    { /* blake2s_256 */
        {
            "69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9",
            "b480c25c1e06eea9e9c3e36754715cf0958e4d14b22a8c2a7bc34ebf75208602",
            "9b3be5344b255a7faed41eb2093aa10f62ba6168d8ad848fcc88e2a376708561",
            "3a588690acdc77ad0dba26e77d650a7299c52cc08c4f73aee671168fc2e65a57",
            "068755ee1119ab011243989482ec4e43fd9e876589c579d6266d606afe5fd785",
            "80e0f09406f9cd33bbe42c62eab741682703b33ce51964ab0195299fd60e693f",
            "97f69df7ec4c5dd4c439bb23fef627538f56fab6bac81d7346fd903571658d12",
            "5d81350814cb4c05fa5e002a7e367b20a6debbc6924748065ff216797a863e73",
            "a3d9c837eb12dc6ec0f9ca13774d83a0e0c0de0373d80d10c6450ffc5e12ca33",
            "99f2c5dc758751d0d1bd07309a2d7a97f1bd3dea153fb7daa07476a45e87e3c8",
        },
        {
            "867954c29c2838dd775b6d3645e41909ac599afc4dde379a2c9c3c7bf8ea4a25",
            "69e182ac437a1ed4c55b636bbf61a4a7fe28782631d88b977f125d2715db133b",
            "0f0c068b11cf1c396400e69b866589b81b5f8ff67c71517726f815001714123b",
            "21f31290a6d82ae18a4564cd08949b90f0237c4058f9b5fff74145a4d02646a0",
            "7ef521c6070deac5a771235ee7b82bb8b05d3fc604fa4c927056af50fade36e0",
            "3d35f0310ea323250040955f1510c561559ae4231fd9d7ef8278d26651bb7696",
            "1803c0d0fd641d499ca2b8031c4080bd94822fd93296009739dcfed6332cecc7",
            "c69a2a139248ed9156deaeaaf0620d143bad07f052c43611a30df61de07902fc",
            "8877632ef79b6d5dc6cb99c01fb12cd5c7f6232d3d9d3d40df240b899e0d9ba0",
            "ab6a492922ee08ce3bddd76f0082865e7063df3cc7f9d6c3b03336c51f6556fa",
        },
        {
            "dd56ad29f0624bf76ce0bd024487b2606d90060d3e09b4026459fdb6245ba785",
            "3b392df498cefbb5ff05bfcbc08597ddf9514629b1231fe3f397e14423eff7ef",
            "f6a4e5aa4ba0f41637a0d0d32bce83f8eaf8977dbbd5790ca09a49c1165401e5",
            "76a64ae45a6fffce78b22474e48e0e4b1dc5b5847733f43a055c25054ce3b136",
            "ffa18166a117ac57aaabf0b89a474238580685fc420519c02838a99d0e6a1ca1",
            "bd3db98bf2f2483bc1ff73ada3570d238794e32518a3469b5bb04730f6596c9c",
            "25a6ac69203c7348d8bf2b5199b3282a4bd319e9c45bfba70f78057e8500b8fe",
            "e5e5cb6607154897534c978fefa84e0f540fc0da91d93e86f566067582989101",
            "4ce706c5a0d0b22bef0c5af48fdbb6b2ebeaa011ed265b48c7e6ecbde5a4c08a",
            "6b1644ef1cb98498a29334ea97b447a717cd2f2635d4d67a5ac76a6a1920a67e",
        },
    },
    { /* blake2s_224 */
        {
            "1fa1291e65248b37b3433475b2a0dd63d54a11ecc4e3e034e7bc1ef4",
            "272fb03cd343a7325124a2ef392f76d53ab53e981f57624cc0f69f60",
            "01a70dac7c206523393f939735e012d4d956388b24fb31efb431662d",
            "c207b8b117ed5d74fca3005f71d5cedf3463ded1458fc253eef5594a",
            "ee980ddf0d2521192c28561cabffc4d4e3d7851dc1b2b897dcbffa59",
            "d85b944c213c7270d3ad47c2285cdb8d1dd6393a01ed021774d98c3a",
            "812b61bbe248f4cb92e22e784ad0835a1f5d1e5e909efc72ad8be63f",
            "321e7a19d8e8d0ca2435561e824c226b2f0c65807bd131f41422d200",
            "d14983db405654aa8ae4d96476dbb83f3192614ed00a951c861ae5e6",
            "60a738f2ee3fae8c14539bd521b56374863f72480e519eb64337e720",
        },
        {
            "0607666eb7c575ef392c3b8b309fa1356faaaa8116aa83366d5768ed",
            "93c321c59cedc7939853eb1e3686dd132dcbdc9008c0f3b66d88d36f",
            "614d3b97154cd0e447f58ee420ef4739256d91440e5ad29c1c2ac4fc",
            "9d8cf09ba0a62d9ed36af9a0d3d75c2901ceedab59dd388da070c24c",
            "2774a3c4f3fb0e9bb77249dd30ee4b3785aaf8f9dc22916f541238e0",
            "9d45e6eac5c44e6c8043458d5b6281a97e6c8cce244d130e5e6d7489",
            "ac026af0fc5b9d53d173602e7fcff52a321307de3664cfaf603312bd",
            "98e8934f209705926bb88af81c35f0272784c5dcf6666f958b5882d8",
            "720eb77e2b8ee4f4c1531f8011403992a4b4960cfe1d8de2c758dbe2",
            "06b7de66c08d5b153016a32d644bf5a830fb240517d548d2afbd4104",
        },
        {
            "c5e3699d9867c41078df0560706ef2e28bd0eca214dca565755910b3",
            "e3086d706443c10ea4325c26f11c63de33237fae34644ad04865ecdc",
            "7e1c6f35a27efe6cd2597782a4db4b2ec94b4892785bc55118ee8093",
            "fcc6d2b9284a2a1a77d8c6707f77578134e275082d7db207d44b292f",
            "f2d3f5b4fa732c567ecea6684068298a2e8a7ec564ea49eb6bae824b",
            "97675092ee5c439cd0e32742788fd5b03346c5e911be4b9c23fde2c2",
            "cc2e75faa13672d539eabf2fd454f3d3fda439f1f12a63b13bff8728",
            "94f492f8d37a99ce7f5bd3432d586c1266b60bb6b3e18be5e42a8256",
            "982e1ecd3425c92a8bd9b823e0fd55ef1b46fc1207718563a33b66e2",
            "2d6453e75bc5ce6b57b8965dd6603c405a79d844a35c5c2187b2f1fb",
        },
    },
    { /* blake2s_160 */
        {
            "354c9c33f735962418bdacb9479873429c34916f",
            "5a98eac1af4bb00a1fefe00014b0b82535c08a6c",
            "70c2a37aa6743129a206e59805811726a74ce17d",
            "453c268e60838748ece20a9193e2473129109026",
            "bc864e62a1b8e6677e7c7138883d37cdf47c8cbc",
            "a23fe9717065c76d6af7da4d530d8da3d88db7df",
            "52c711adb978df1c938c1f96dcb9452636e3d606",
            "5d36f471170805b68a2c9d682d0861195d100827",
            "c6c21915afe5915ac053da72acee1b9b983c99b2",
            "379ed46969782c5f27cc9291f6495a4bc26a0af8",
        },
        {
            "9448d7a262f173931044eb2ab5454fff4241a538",
            "38b15e86b3129556f4d3f8f1d218b3147b0ef2ea",
            "821d178e70976e2ac9e7952265aa4d7d19b2fb65",
            "13e628f0d8ac0ec00fdda99404e3a7e823b01246",
            "e655b0ad0fc3c52683f1db53d596c2b801265d65",
            "a33b5ea744edb71f2658cca82e8804392c0cd4d2",
            "44f5e54e9e176d6ba80c46b282eaa4d7bd0acaa7",
            "de42af08b12cc28a63c25d11f53ff36c7432c125",
            "9a80471e2ac56af42213f291a255707e38b1c504",
            "46adcbef7c7f1f89b154e59c9a72b778a8ebb789",
        },
        {
            "9fed31bf47036943b66c1c59c47dcfd99ab34289",
            "5f7baf2f56067e030a51d8de32d325ec21c74c56",
            "0c4b33584481d0044df8b0d638845fdcd10b7065",
            "ee5e9a18fc6259ca7c20317f17b87ff2032213ec",
            "e2e32e0984e5ce4bfefa9ffd976957c58b81b954",
            "effbec397e9cc40644a27b86acf10dce8155dc36",
            "cc31a592eafab17fa0030fbdb426f034085e8e8b",
            "0bfb1ee45b506b836a6cc1ae0333740def5c3c58",
            "0bcef7f066194b0230e2a6180f7443ceb6282760",
            "0b3a236f6832991f4b85b1ee310a88a8aad89627",
        },
    },
    { /* blake2s_128 */
        {
            "64550d6ffe2c0a01a14aba1eade0200c",
            "8d7b89d5c0ff1fb0627835dc36bb4c24",
            "a4d10717f3c85fe5bb36dfd520660cf5",
            "9da3ce53753693ff11cfdf7eea7c8257",
            "4c5b6ab9e04bc0b502d58d91ed20f2ef",
            "6f7cd5be066d976e84993408f36a6c47",
            "ca7db6dc21695bf85fa5469227c25df1",
            "96198ec2edab2ebab7dcba6428fad5f4",
            "5deb542f97dfb0ae0af12d1ec9823698",
            "80eb3f84dcbebf35cbb94f99ca975c32",
        },
        {
            "4d890a99ff46c0162a98bd3bc93e8bf1",
            "2ab96fd31613c3609e9ff62695455b51",
            "18b2cea6442e37df93e4b8df8cf45362",
            "023fda7536ce4f4c253e3767678f8c29",
            "ef06c58be62ad6254a01d5ea27efacb1",
            "c727aac8fd7ba56948ffa4c95ac78817",
            "6846d60c82c18322f2a1bc92713dc2c1",
            "d5676485252e7d5494ca07e165402a27",
            "229dab57f067312c5fd32fa79e529e23",
            "2628877a6fc4d524e49b85fd90401608",
        },
        {
            "5bb934ab3e1a0f541b5c0ea8c90cfd17",
            "b1c2612cf4284c4f926c2cc5aa803aa4",
            "8c34b88bce4c9d96701b9d9dcf564212",
            "205413faba6b6f3aacffe2556d704059",
            "f7ea494d98d239e582e6b04cdcd4e12b",
            "0f216c8bd76a523a7cadc7d3662bf2bd",
            "dca02b3c685b9d71150ea509f1f491c9",
            "fb20b49df16320a4be5b35cb3632719e",
            "a847333883ef070c045c851d693a71d2",
            "ace672c18064ff94e56505bc480a959d",
        },
    },
};

#define MSGMAX 1200
static uint8_t msgbuf[MSGMAX];
static uint8_t keybuf[64];

/* A state, big enough for either family. */
typedef struct {
  uint64_t acc[8];
  uint8_t buf[128];
  size_t tot;
} state;

static void hash_in_chunks(const alg *a, state *st, size_t key_len,
                           const uint8_t *msg, size_t msg_len, size_t chunk,
                           uint8_t *out) {
  a->init(st->acc, st->buf, &st->tot, keybuf, key_len);
  size_t i = 0;
  while (i < msg_len) {
    size_t n = msg_len - i < chunk ? msg_len - i : chunk;
    a->update(st->acc, st->buf, &st->tot, (uint8_t *)msg + i, n);
    i += n;
  }
  a->digest(st->acc, st->buf, &st->tot, out);
}

static void check(const alg *a, size_t key_len, size_t msg_len, size_t chunk,
                  const char *expect) {
  state st;
  uint8_t out[64];
  char got[129];

  memset(&st, 0, sizeof st);
  memset(out, 0, sizeof out);
  hash_in_chunks(a, &st, key_len, msgbuf, msg_len, chunk, out);
  hex(got, out, a->digest_len);

  if (strcmp(got, expect) != 0) {
    printf("  FAIL %s k=%zu m=%zu chunk=%zu\n    got      %s\n"
           "    expected %s\n",
           a->name, key_len, msg_len, chunk, got, expect);
    failures++;
  }
}

/* digest leaves the state usable: two digests agree, and an update after a
 * digest continues the same message. */
static void check_lifecycle(void) {
  for (int k = 0; k < NALG; k++) {
    const alg *a = &algs[k];
    state st;
    uint8_t d1[64], d2[64], d3[64], ref[64];
    char got[129], want[129];

    memset(&st, 0, sizeof st);
    a->init(st.acc, st.buf, &st.tot, keybuf, a->key_max);
    a->update(st.acc, st.buf, &st.tot, msgbuf, 100);
    a->digest(st.acc, st.buf, &st.tot, d1);
    a->digest(st.acc, st.buf, &st.tot, d2);

    if (memcmp(d1, d2, a->digest_len) != 0) {
      printf("  FAIL %s digest is not idempotent\n", a->name);
      failures++;
      continue;
    }

    /* Carry on to 300 bytes and compare with hashing all 300 at once. */
    a->update(st.acc, st.buf, &st.tot, msgbuf + 100, 200);
    a->digest(st.acc, st.buf, &st.tot, d3);

    memset(&st, 0, sizeof st);
    hash_in_chunks(a, &st, a->key_max, msgbuf, 300, 300, ref);

    hex(got, d3, a->digest_len);
    hex(want, ref, a->digest_len);
    if (strcmp(got, want) != 0) {
      printf("  FAIL %s update after digest\n    got      %s\n"
             "    expected %s\n",
             a->name, got, want);
      failures++;
    } else {
      printf("  ok   %s digest is idempotent and resumable\n", a->name);
    }
  }
}

int main(void) {
  for (size_t i = 0; i < sizeof msgbuf; i++)
    msgbuf[i] = (uint8_t)((i * 7 + 11) & 0xff);
  for (size_t i = 0; i < sizeof keybuf; i++)
    keybuf[i] = (uint8_t)((i * 3 + 5) & 0xff);

  int checks = 0;
  for (int k = 0; k < NALG; k++) {
    const alg *a = &algs[k];
    size_t key_lens[NKEY] = {0, 1, a->key_max};
    for (int j = 0; j < NKEY; j++)
      for (int m = 0; m < NLEN; m++)
        for (size_t c = 0; c < NCHUNKS; c++) {
          check(a, key_lens[j], msg_lens[m], chunks[c], expected[k][j][m]);
          checks++;
        }
    printf("  ok   %s (%d key lengths x %d message lengths x %zu chunk "
           "sizes)\n",
           a->name, NKEY, NLEN, NCHUNKS);
  }

  check_lifecycle();

  if (failures == 0) {
    printf("test_blake2_streaming: all %d checks passed\n", checks);
    return 0;
  }
  printf("test_blake2_streaming: %d failures\n", failures);
  return 1;
}

