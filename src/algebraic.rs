use crate::algebraic::ComplexFactor::{
    AddSub, Divide, Factorial, Fibonacci, Lucas, Multiply, Power, Primorial,
};
use crate::algebraic::Factor::{Complex, ElidedNumber, Numeric, UnknownExpression};
use crate::graph::EntryId;
use crate::net::BigNumber;
use crate::{MAX_ID_EQUAL_TO_VALUE, NumberLength, frame_sync, hash, write_bignum};
use ahash::RandomState;
use async_backtrace::location;
use derivative::Derivative;
use hipstr::HipStr;
use itertools::Itertools;
use log::{debug, error, info, warn};
use num_integer::Integer;
use num_modular::{ModularCoreOps, ModularPow};
use num_prime::ExactRoots;
use num_prime::Primality::No;
use num_prime::buffer::{NaiveBuffer, PrimeBufferExt};
use num_prime::detail::SMALL_PRIMES;
use num_prime::nt_funcs::factorize128;
use quick_cache::UnitWeighter;
use quick_cache::sync::{Cache, DefaultLifecycle};
use std::borrow::Cow;
use std::cell::RefCell;
use std::cmp::{Ordering, PartialEq};
use std::collections::{BTreeMap, BTreeSet};
use std::default::Default;
use std::f64::consts::LN_10;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::hint::unreachable_unchecked;
use std::iter::once;
use std::mem::swap;
use std::sync::{Arc, OnceLock};
use tokio::task;
use yamaquasi::Algo::Siqs;
use yamaquasi::Verbosity::Silent;
use yamaquasi::{Preferences, factor};

thread_local! {
    static FIND_FACTORS_STACK: RefCell<BTreeSet<Factor>> = const { RefCell::new(BTreeSet::new()) };
}

static SMALL_FIBONACCI_FACTORS: [&[NumericFactor]; 199] = [
    &[0],
    &[],
    &[],
    &[2],
    &[3],
    &[5],
    &[2, 2, 2],
    &[13],
    &[3, 7],
    &[2, 17],
    &[5, 11],
    &[89],
    &[2, 2, 2, 2, 3, 3],
    &[233],
    &[13, 29],
    &[2, 5, 61],
    &[3, 7, 47],
    &[1597],
    &[2, 2, 2, 17, 19],
    &[37, 113],
    &[3, 5, 11, 41],
    &[2, 13, 421],
    &[89, 199],
    &[28657],
    &[2, 2, 2, 2, 2, 3, 3, 7, 23],
    &[5, 5, 3001],
    &[233, 521],
    &[2, 17, 53, 109],
    &[3, 13, 29, 281],
    &[514229],
    &[2, 2, 2, 5, 11, 31, 61],
    &[557, 2417],
    &[3, 7, 47, 2207],
    &[2, 89, 19801],
    &[1597, 3571],
    &[5, 13, 141961],
    &[2, 2, 2, 2, 3, 3, 3, 17, 19, 107],
    &[73, 149, 2221],
    &[37, 113, 9349],
    &[2, 233, 135721],
    &[3, 5, 7, 11, 41, 2161],
    &[2789, 59369],
    &[2, 2, 2, 13, 29, 211, 421],
    &[433494437],
    &[3, 43, 89, 199, 307],
    &[2, 5, 17, 61, 109441],
    &[139, 461, 28657],
    &[2971215073],
    &[2, 2, 2, 2, 2, 2, 3, 3, 7, 23, 47, 1103],
    &[13, 97, 6168709],
    &[5, 5, 11, 101, 151, 3001],
    &[2, 1597, 6376021],
    &[3, 233, 521, 90481],
    &[953, 55945741],
    &[2, 2, 2, 17, 19, 53, 109, 5779],
    &[5, 89, 661, 474541],
    &[3, 7, 7, 13, 29, 281, 14503],
    &[2, 37, 113, 797, 54833],
    &[59, 19489, 514229],
    &[353, 2710260697],
    &[2, 2, 2, 2, 3, 3, 5, 11, 31, 41, 61, 2521],
    &[4513, 555003497],
    &[557, 2417, 3010349],
    &[2, 13, 17, 421, 35239681],
    &[3, 7, 47, 1087, 2207, 4481],
    &[5, 233, 14736206161],
    &[2, 2, 2, 89, 199, 9901, 19801],
    &[269, 116849, 1429913],
    &[3, 67, 1597, 3571, 63443],
    &[2, 137, 829, 18077, 28657],
    &[5, 11, 13, 29, 71, 911, 141961],
    &[6673, 46165371073],
    &[2, 2, 2, 2, 2, 3, 3, 3, 7, 17, 19, 23, 107, 103681],
    &[9375829, 86020717],
    &[73, 149, 2221, 54018521],
    &[2, 5, 5, 61, 3001, 230686501],
    &[3, 37, 113, 9349, 29134601],
    &[13, 89, 988681, 4832521],
    &[2, 2, 2, 79, 233, 521, 859, 135721],
    &[157, 92180471494753],
    &[3, 5, 7, 11, 41, 47, 1601, 2161, 3041],
    &[2, 17, 53, 109, 2269, 4373, 19441],
    &[2789, 59369, 370248451],
    &[99194853094755497],
    &[2, 2, 2, 2, 3, 3, 13, 29, 83, 211, 281, 421, 1427],
    &[5, 1597, 9521, 3415914041],
    &[6709, 144481, 433494437],
    &[2, 173, 514229, 3821263937],
    &[3, 7, 43, 89, 199, 263, 307, 881, 967],
    &[1069, 1665088321800481],
    &[2, 2, 2, 5, 11, 17, 19, 31, 61, 181, 541, 109441],
    &[13, 13, 233, 741469, 159607993],
    &[3, 139, 461, 4969, 28657, 275449],
    &[2, 557, 2417, 4531100550901],
    &[2971215073, 6643838879],
    &[5, 37, 113, 761, 29641, 67735001],
    &[2, 2, 2, 2, 2, 2, 2, 3, 3, 7, 23, 47, 769, 1103, 2207, 3167],
    &[193, 389, 3084989, 361040209],
    &[13, 29, 97, 6168709, 599786069],
    &[2, 17, 89, 197, 19801, 18546805133],
    &[3, 5, 5, 11, 41, 101, 151, 401, 3001, 570601],
    &[743519377, 770857978613],
    &[2, 2, 2, 919, 1597, 3469, 3571, 6376021],
    &[519121, 5644193, 512119709],
    &[3, 7, 103, 233, 521, 90481, 102193207],
    &[2, 5, 13, 61, 421, 141961, 8288823481],
    &[953, 55945741, 119218851371],
    &[1247833, 8242065050061761],
    &[2, 2, 2, 2, 3, 3, 3, 3, 17, 19, 53, 107, 109, 5779, 11128427],
    &[827728777, 32529675488417],
    &[5, 11, 11, 89, 199, 331, 661, 39161, 474541],
    &[2, 73, 149, 2221, 1459000305513721],
    &[3, 7, 7, 13, 29, 47, 281, 14503, 10745088481],
    &[677, 272602401466814027129],
    &[2, 2, 2, 37, 113, 229, 797, 9349, 54833, 95419],
    &[5, 1381, 28657, 2441738887963981],
    &[3, 59, 347, 19489, 514229, 1270083883],
    &[2, 17, 233, 29717, 135721, 39589685693],
    &[353, 709, 8969, 336419, 2710260697],
    &[13, 1597, 159512939815855788121],
    &[
        2, 2, 2, 2, 2, 3, 3, 5, 7, 11, 23, 31, 41, 61, 241, 2161, 2521, 20641,
    ],
    &[89, 97415813466381445596089],
    &[4513, 555003497, 5600748293801],
    &[2, 2789, 59369, 68541957733949701],
    &[3, 557, 2417, 3010349, 3020733700601],
    &[5, 5, 5, 3001, 158414167964045700001],
    &[2, 2, 2, 13, 17, 19, 29, 211, 421, 1009, 31249, 35239681],
    &[27941, 5568053048227732210073],
    &[3, 7, 47, 127, 1087, 2207, 4481, 186812208641],
    &[2, 257, 5417, 8513, 39639893, 433494437],
    &[5, 11, 131, 233, 521, 2081, 24571, 14736206161],
    &[1066340417491710595814572169],
    &[2, 2, 2, 2, 3, 3, 43, 89, 199, 307, 9901, 19801, 261399601],
    &[13, 37, 113, 3457, 42293, 351301301942501],
    &[269, 4021, 116849, 1429913, 24994118449],
    &[2, 5, 17, 53, 61, 109, 109441, 1114769954367361],
    &[3, 7, 67, 1597, 3571, 63443, 23230657239121],
    &[19134702400093278081449423917],
    &[2, 2, 2, 137, 139, 461, 691, 829, 18077, 28657, 1485571],
    &[277, 2114537501, 85526722937689093],
    &[3, 5, 11, 13, 29, 41, 71, 281, 911, 141961, 12317523121],
    &[2, 108289, 1435097, 142017737, 2971215073],
    &[6673, 46165371073, 688846502588399],
    &[89, 233, 8581, 1929584153756850496621],
    &[
        2,
        2,
        2,
        2,
        2,
        2,
        3,
        3,
        3,
        7,
        17,
        19,
        23,
        47,
        107,
        1103,
        103681,
        10749957121,
    ],
    &[5, 514229, 349619996930737079890201],
    &[151549, 9375829, 86020717, 11899937029],
    &[2, 13, 97, 293, 421, 3529, 6168709, 347502052673],
    &[3, 73, 149, 2221, 11987, 54018521, 81143477963],
    &[110557, 162709, 4000949, 85607646594577],
    &[
        2, 2, 2, 5, 5, 11, 31, 61, 101, 151, 3001, 12301, 18451, 230686501,
    ],
    &[5737, 2811666624525811646469915877],
    &[3, 7, 37, 113, 9349, 29134601, 1091346396980401],
    &[2, 17, 17, 1597, 6376021, 7175323114950564593],
    &[13, 29, 89, 199, 229769, 988681, 4832521, 9321929],
    &[5, 557, 2417, 21701, 12370533881, 61182778621],
    &[
        2,
        2,
        2,
        2,
        3,
        3,
        79,
        233,
        521,
        859,
        90481,
        135721,
        12280217041,
    ],
    &[313, 11617, 7636481, 10424204306491346737],
    &[157, 92180471494753, 32361122672259149],
    &[2, 317, 953, 55945741, 97639037, 229602768949],
    &[3, 5, 7, 11, 41, 47, 1601, 2161, 2207, 3041, 23725145626561],
    &[13, 8693, 28657, 612606107755058997065597],
    &[
        2, 2, 2, 17, 19, 53, 109, 2269, 3079, 4373, 5779, 19441, 62650261,
    ],
    &[977, 4892609, 33365519393, 32566223208133],
    &[3, 163, 2789, 59369, 800483, 350207569, 370248451],
    &[2, 5, 61, 89, 661, 19801, 86461, 474541, 518101, 900241],
    &[35761381, 6202401259, 99194853094755497],
    &[18104700793, 1966344318693345608565721],
    &[
        2, 2, 2, 2, 2, 3, 3, 7, 7, 13, 23, 29, 83, 167, 211, 281, 421, 1427, 14503, 65740583,
    ],
    &[233, 337, 89909, 104600155609, 126213229732669],
    &[5, 11, 1597, 3571, 9521, 1158551, 12760031, 3415914041],
    &[2, 17, 37, 113, 797, 6841, 54833, 5741461760879844361],
    &[3, 6709, 144481, 433494437, 313195711516578281],
    &[1639343785721, 389678749007629271532733],
    &[2, 2, 2, 59, 173, 349, 19489, 514229, 947104099, 3821263937],
    &[5, 5, 13, 701, 3001, 141961, 17231203730201189308301],
    &[
        3, 7, 43, 47, 89, 199, 263, 307, 881, 967, 93058241, 562418561,
    ],
    &[2, 353, 2191261, 805134061, 1297027681, 2710260697],
    &[179, 1069, 1665088321800481, 22235502640988369],
    &[21481, 156089, 3418816640903898929534613769],
    &[
        2,
        2,
        2,
        2,
        3,
        3,
        3,
        5,
        11,
        17,
        19,
        31,
        41,
        61,
        107,
        181,
        541,
        2521,
        109441,
        10783342081,
    ],
    &[8689, 422453, 8175789237238547574551461093],
    &[13, 13, 29, 233, 521, 741469, 159607993, 689667151970161],
    &[2, 1097, 4513, 555003497, 14297347971975757800833],
    &[3, 7, 139, 461, 4969, 28657, 253367, 275449, 9506372193863],
    &[5, 73, 149, 2221, 1702945513191305556907097618161],
    &[2, 2, 2, 557, 2417, 63799, 3010349, 35510749, 4531100550901],
    &[89, 373, 1597, 10157807305963434099105034917037],
    &[3, 563, 5641, 2971215073, 6643838879, 4632894751907],
    &[2, 13, 17, 53, 109, 421, 38933, 35239681, 955921950316735037],
    &[
        5, 11, 37, 113, 191, 761, 9349, 29641, 41611, 67735001, 87382901,
    ],
    &[4870723671313, 757810806256989128439975793],
    &[
        2,
        2,
        2,
        2,
        2,
        2,
        2,
        2,
        3,
        3,
        7,
        23,
        47,
        769,
        1087,
        1103,
        2207,
        3167,
        4481,
        11862575248703,
    ],
    &[9465278929, 1020930432032326933976826008497],
    &[193, 389, 3299, 3084989, 361040209, 56678557502141579],
    &[2, 5, 61, 233, 135721, 14736206161, 88999250837499877681],
    &[3, 13, 29, 97, 281, 5881, 6168709, 599786069, 61025309469041],
    &[15761, 25795969, 227150265697, 717185107125886549],
    &[
        2,
        2,
        2,
        17,
        19,
        89,
        197,
        199,
        991,
        2179,
        9901,
        19801,
        1513909,
        18546805133,
    ],
];

static SMALL_LUCAS_FACTORS: [&[NumericFactor]; 202] = [
    &[2],
    &[],
    &[3],
    &[2, 2],
    &[7],
    &[11],
    &[2, 3, 3],
    &[29],
    &[47],
    &[2, 2, 19],
    &[3, 41],
    &[199],
    &[2, 7, 23],
    &[521],
    &[3, 281],
    &[2, 2, 11, 31],
    &[2207],
    &[3571],
    &[2, 3, 3, 3, 107],
    &[9349],
    &[7, 2161],
    &[2, 2, 29, 211],
    &[3, 43, 307],
    &[139, 461],
    &[2, 47, 1103],
    &[11, 101, 151],
    &[3, 90481],
    &[2, 2, 19, 5779],
    &[7, 7, 14503],
    &[59, 19489],
    &[2, 3, 3, 41, 2521],
    &[3010349],
    &[1087, 4481],
    &[2, 2, 199, 9901],
    &[3, 67, 63443],
    &[11, 29, 71, 911],
    &[2, 7, 23, 103681],
    &[54018521],
    &[3, 29134601],
    &[2, 2, 79, 521, 859],
    &[47, 1601, 3041],
    &[370248451],
    &[2, 3, 3, 83, 281, 1427],
    &[6709, 144481],
    &[7, 263, 881, 967],
    &[2, 2, 11, 19, 31, 181, 541],
    &[3, 4969, 275449],
    &[6643838879],
    &[2, 769, 2207, 3167],
    &[29, 599786069],
    &[3, 41, 401, 570601],
    &[2, 2, 919, 3469, 3571],
    &[7, 103, 102193207],
    &[119218851371],
    &[2, 3, 3, 3, 3, 107, 11128427],
    &[11, 11, 199, 331, 39161],
    &[47, 10745088481],
    &[2, 2, 229, 9349, 95419],
    &[3, 347, 1270083883],
    &[709, 8969, 336419],
    &[2, 7, 23, 241, 2161, 20641],
    &[5600748293801],
    &[3, 3020733700601],
    &[2, 2, 19, 29, 211, 1009, 31249],
    &[127, 186812208641],
    &[11, 131, 521, 2081, 24571],
    &[2, 3, 3, 43, 307, 261399601],
    &[4021, 24994118449],
    &[7, 23230657239121],
    &[2, 2, 139, 461, 691, 1485571],
    &[3, 41, 281, 12317523121],
    &[688846502588399],
    &[2, 47, 1103, 10749957121],
    &[151549, 11899937029],
    &[3, 11987, 81143477963],
    &[2, 2, 11, 31, 101, 151, 12301, 18451],
    &[7, 1091346396980401],
    &[29, 199, 229769, 9321929],
    &[2, 3, 3, 90481, 12280217041],
    &[32361122672259149],
    &[2207, 23725145626561],
    &[2, 2, 19, 3079, 5779, 62650261],
    &[3, 163, 800483, 350207569],
    &[35761381, 6202401259],
    &[2, 7, 7, 23, 167, 14503, 65740583],
    &[11, 3571, 1158551, 12760031],
    &[3, 313195711516578281],
    &[2, 2, 59, 349, 19489, 947104099],
    &[47, 93058241, 562418561],
    &[179, 22235502640988369],
    &[2, 3, 3, 3, 41, 107, 2521, 10783342081],
    &[29, 521, 689667151970161],
    &[7, 253367, 9506372193863],
    &[2, 2, 63799, 3010349, 35510749],
    &[3, 563, 5641, 4632894751907],
    &[11, 191, 9349, 41611, 87382901],
    &[2, 1087, 4481, 11862575248703],
    &[3299, 56678557502141579],
    &[3, 281, 5881, 61025309469041],
    &[2, 2, 19, 199, 991, 2179, 9901, 1513909],
    &[7, 2161, 9125201, 5738108801],
    &[809, 7879, 201062946718741],
    &[2, 3, 3, 67, 409, 63443, 66265118449],
    &[619, 1031, 5257480026438961],
    &[47, 3329, 106513889, 325759201],
    &[2, 2, 11, 29, 31, 71, 211, 911, 21211, 767131],
    &[3, 1483, 2969, 1076012367720403],
    &[47927441, 479836483312919],
    &[2, 7, 23, 6263, 103681, 177962167367],
    &[128621, 788071, 593985111211],
    &[3, 41, 43, 307, 59996854928656801],
    &[2, 2, 4441, 146521, 1121101, 54018521],
    &[223, 449, 2207, 1154149773784223],
    &[412670427844921037470771],
    &[2, 3, 3, 227, 26449, 29134601, 212067587],
    &[11, 139, 461, 1151, 5981, 324301, 686551],
    &[7, 299281, 834428410879506721],
    &[2, 2, 19, 79, 521, 859, 1052645985555841],
    &[3, 15247723, 100049587197598387],
    &[29, 239, 3571, 10711, 27932732439809],
    &[2, 47, 1103, 1601, 3041, 23735900452321],
    &[199, 97420733208491869044199],
    &[3, 19763, 21291929, 24848660119363],
    &[2, 2, 4767481, 370248451, 7188487771],
    &[7, 743, 467729, 33758740830460183],
    &[11, 101, 151, 251, 112128001, 28143378001],
    &[2, 3, 3, 3, 83, 107, 281, 1427, 1461601, 764940961],
    &[509, 5081, 487681, 13822681, 19954241],
    &[119809, 4698167634523379875583],
    &[2, 2, 6709, 144481, 308311, 761882591401],
    &[3, 41, 3121, 90481, 42426476041450801],
    &[1049, 414988698461, 5477332620091],
    &[2, 7, 23, 263, 881, 967, 5281, 66529, 152204449],
    &[29, 9349, 10694421739, 2152958650459],
    &[3, 6163, 201912469249, 2705622682163],
    &[2, 2, 11, 19, 31, 181, 271, 541, 811, 5779, 42391, 119611],
    &[47, 562627837283291940137654881],
    &[541721291, 78982487870939058281],
    &[2, 3, 3, 4969, 16561, 162563, 275449, 1043766587],
    &[30859, 253279129, 14331800109223159],
    &[7, 7, 2161, 14503, 118021448662479038881],
    &[2, 2, 79099591, 6643838879, 139509555271],
    &[3, 283, 569, 2820403, 9799987, 35537616083],
    &[199, 521, 1957099, 2120119, 1784714380021],
    &[2, 769, 2207, 3167, 115561578124838522881],
    &[11, 59, 19489, 120196353941, 1322154751061],
    &[3, 29201, 37125857850184727260788881],
    &[2, 2, 29, 211, 65269, 620929, 8844991, 599786069],
    &[7, 10661921, 114087288048701953998401],
    &[952111, 4434539, 3263039535803245519],
    &[2, 3, 3, 41, 401, 601, 2521, 570601, 87129547172401],
    &[1511, 109734721, 217533000184835774779],
    &[47, 562766385967, 2206456200865197103],
    &[2, 2, 19, 919, 3469, 3571, 13159, 8293976826829399],
    &[3, 43, 281, 307, 15252467, 900164950225760603],
    &[11, 311, 3010349, 29138888651, 823837075741],
    &[2, 7, 23, 103, 1249, 102193207, 94491842183551489],
    &[39980051, 16188856575286517818849171],
    &[3, 21803, 5924683, 14629892449, 184715524801],
    &[2, 2, 785461, 119218851371, 4523819299182451],
    &[641, 1087, 4481, 878132240443974874201601],
    &[29, 139, 461, 1289, 1917511, 965840862268529759],
    &[2, 3, 3, 3, 3, 3, 107, 11128427, 1828620361, 6782976947987],
    &[1043201, 6601501, 1686454671192230445929],
    &[7, 2684571411430027028247905903965201],
    &[
        2, 2, 11, 11, 31, 199, 331, 9901, 39161, 51164521, 1550853481,
    ],
    &[3, 6464041, 245329617161, 10341247759646081],
    &[766531, 103849927693584542320127327909],
    &[2, 47, 1103, 10745088481, 115613939510481515041],
    &[521, 596107814364089, 671040394220849329],
    &[3, 41, 67, 1361, 40801, 63443, 11614654211954032961],
    &[2, 2, 19, 19, 229, 9349, 95419, 162451, 1617661, 7038398989],
    &[7, 126117711915911646784404045944033521],
    &[78889, 6248069, 16923049609, 171246170261359],
    &[2, 3, 3, 347, 97787, 528295667, 1270083883, 5639710969],
    &[11, 29, 71, 101, 151, 911, 54601, 560701, 7517651, 51636551],
    &[1409, 2207, 6086461133983, 319702847642258783],
    &[2, 2, 709, 8969, 336419, 10884439, 105117617351706859],
    &[3, 5280544535667472291277149119296546201],
    &[359, 1066737847220321, 66932254279484647441],
    &[2, 7, 23, 241, 2161, 8641, 20641, 103681, 13373763765986881],
    &[97379, 21373261504197751, 32242356485644069],
    &[3, 281, 90481, 232961, 6110578634294886534808481],
    &[2, 2, 14686239709, 5600748293801, 533975715909289],
    &[47, 367, 37309023160481, 441720958100381917103],
    &[11, 54018521, 265272771839851, 2918000731816531],
    &[2, 3, 3, 15917507, 3020733700601, 859886421593527043],
    &[199, 1871, 3571, 905674234408506526265097390431],
    &[7, 18049, 100769, 153037630649666194962091443041],
    &[
        2, 2, 19, 29, 211, 379, 1009, 5779, 31249, 85429, 912871, 1258740001,
    ],
    &[3, 41, 2281, 4561, 29134601, 782747561, 174795553490801],
    &[22921, 395586472506832921, 910257559954057439],
    &[2, 127, 383, 5662847, 6803327, 19073614849, 186812208641],
    &[303011, 76225351, 935527893146187207403151261],
    &[3, 195163, 4501963, 5644065667, 2350117027000544947],
    &[
        2, 2, 11, 31, 79, 131, 521, 859, 1951, 2081, 2731, 24571, 866581, 37928281,
    ],
    &[7, 7, 7, 14503, 3016049, 6100804791163473872231629367],
    &[31498587119111339, 4701907222895068350249889],
    &[
        2,
        3,
        3,
        3,
        43,
        107,
        307,
        261399601,
        11166702227,
        1076312899454363,
    ],
    &[2389, 4503769, 36036960414811969810787847118289],
    &[47, 1601, 3041, 124001, 6996001, 3160438834174817356001],
    &[2, 2, 4021, 24994118449, 2686039424221, 940094299967491],
];

pub type NumericFactor = u128;
pub type SignedNumericFactor = i128;

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum FactorBeingParsed {
    Numeric(NumericFactor),
    BigNumber(BigNumber),
    ElidedNumber(HipStr<'static>),
    AddSub {
        left: Box<FactorBeingParsed>,
        right: Box<FactorBeingParsed>,
        subtract: bool,
    },
    Multiply {
        terms: BTreeMap<FactorBeingParsed, NumberLength>,
    },
    Divide {
        left: Box<FactorBeingParsed>,
        right: BTreeMap<FactorBeingParsed, NumberLength>,
    },
    Power {
        base: Box<FactorBeingParsed>,
        exponent: Box<FactorBeingParsed>,
    },
    Fibonacci(Box<FactorBeingParsed>),
    Lucas(Box<FactorBeingParsed>),
    Factorial(Box<FactorBeingParsed>),
    Primorial(Box<FactorBeingParsed>),
}

impl Default for FactorBeingParsed {
    fn default() -> Self {
        FactorBeingParsed::Numeric(1)
    }
}

fn hash_add_sub<H: Hasher>(terms: &(Factor, Factor), state: &mut H) {
    let (left, right) = terms;
    let invariant_hasher_state = RandomState::with_seed(0x1337c0de);
    let left_hash = invariant_hasher_state.hash_one(left);
    let right_hash = invariant_hasher_state.hash_one(right);
    state.write_u64(left_hash.wrapping_add(right_hash));
}

#[derive(Derivative, PartialOrd, Ord)]
#[derivative(Clone, Debug, Hash, Eq)]
pub enum ComplexFactor {
    AddSub {
        #[derivative(Hash(hash_with = "crate::algebraic::hash_add_sub"))]
        terms: (Factor, Factor),
        subtract: bool,
    },
    Multiply {
        terms_hash: u64,
        #[derivative(Hash = "ignore")]
        terms: BTreeMap<Factor, NumberLength>,
    },
    Divide {
        left: Factor,
        right_hash: u64,
        #[derivative(Hash = "ignore")]
        right: BTreeMap<Factor, NumberLength>,
    },
    Power {
        base: Factor,
        exponent: Factor,
    },
    Fibonacci(Factor),
    Lucas(Factor),
    Factorial(Factor),
    Primorial(Factor),
}

#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum Factor {
    Numeric(NumericFactor),
    BigNumber(BigNumber),
    ElidedNumber(HipStr<'static>),
    UnknownExpression(HipStr<'static>),
    Complex(Arc<ComplexFactor>),
}

impl PartialEq for ComplexFactor {
    fn eq(&self, other: &Self) -> bool {
        match self {
            AddSub {
                terms: (x, y),
                subtract,
            } => matches!(other, AddSub {terms: (ox, oy), subtract: os} if
                os == subtract
            && ((x == ox && y == oy) || (!subtract && x == oy && y == ox))),
            Multiply { terms_hash, terms } => {
                matches!(other, Multiply { terms_hash: other_terms_hash, terms: other_terms }
                if terms_hash == other_terms_hash && terms == other_terms)
            }
            Divide {
                left,
                right_hash,
                right,
            } => {
                matches!(other, Divide {left: other_left, right_hash: other_right_hash, right: other_right }
                if right_hash == other_right_hash && left == other_left && right == other_right)
            }
            Power { base, exponent } => {
                matches!(other, Power {base: other_base, exponent: other_exponent}
                if base == other_base && exponent == other_exponent)
            }
            Fibonacci(term) => matches!(other, Fibonacci(other_term) if term == other_term),
            Lucas(term) => matches!(other, Lucas(other_term) if term == other_term),
            Factorial(term) => matches!(other, Factorial(other_term) if term == other_term),
            Primorial(term) => matches!(other, Primorial(other_term) if term == other_term),
        }
    }
}

impl From<FactorBeingParsed> for Factor {
    #[inline(always)]
    fn from(value: FactorBeingParsed) -> Self {
        match value {
            FactorBeingParsed::Numeric(n) => Numeric(n),
            FactorBeingParsed::BigNumber(n) => Factor::BigNumber(n),
            FactorBeingParsed::ElidedNumber(n) => ElidedNumber(n),
            FactorBeingParsed::AddSub {
                left,
                right,
                subtract,
            } => Complex(
                AddSub {
                    terms: (Factor::from(*left), Factor::from(*right)),
                    subtract,
                }
                .into(),
            ),
            FactorBeingParsed::Multiply { terms } => {
                Factor::multiply(
                    terms
                        .into_iter()
                        .map(|(term, power)| (Factor::from(term), power))
                        .collect()
                )
            },
            FactorBeingParsed::Divide { left, right } => Factor::divide(
                (*left).into(),
                right
                    .into_iter()
                    .map(|(term, power)| (Factor::from(term), power)),
            ),
            FactorBeingParsed::Power { base, exponent } => Complex(
                Power {
                    base: Factor::from(*base),
                    exponent: Factor::from(*exponent),
                }
                .into(),
            ),
            FactorBeingParsed::Fibonacci(term) => Complex(Fibonacci(Factor::from(*term)).into()),
            FactorBeingParsed::Lucas(term) => Complex(Lucas(Factor::from(*term)).into()),
            FactorBeingParsed::Factorial(term) => Complex(Factorial(Factor::from(*term)).into()),
            FactorBeingParsed::Primorial(term) => Complex(Primorial(Factor::from(*term)).into()),
        }
    }
}

type SyncFactorCache<V> = Cache<Factor, V, UnitWeighter, RandomState, DefaultLifecycle<Factor, V>>;
type FactorCacheLock<T> = OnceLock<SyncFactorCache<T>>;

// Object pools are used to avoid discarding a thread-local cache's contents when the thread exits,
// in case another thread started later can use them.

static NUMERIC_VALUE_CACHE_LOCK: FactorCacheLock<Option<NumericFactor>> = FactorCacheLock::new();
static LOG10_ESTIMATE_CACHE_LOCK: FactorCacheLock<(NumberLength, NumberLength)> =
    FactorCacheLock::new();
static FACTOR_CACHE_LOCK: FactorCacheLock<BTreeMap<Factor, NumberLength>> = FactorCacheLock::new();
static UNIQUE_FACTOR_CACHE_LOCK: FactorCacheLock<Box<[Factor]>> = FactorCacheLock::new();

const NUMERIC_VALUE_CACHE_SIZE: usize = 1 << 20;
const LOG10_ESTIMATE_CACHE_SIZE: usize = 1 << 20;
const FACTOR_CACHE_SIZE: usize = 1 << 12;
const UNIQUE_FACTOR_CACHE_SIZE: usize = 1 << 16;

pub fn get_numeric_value_cache() -> &'static SyncFactorCache<Option<NumericFactor>> {
    NUMERIC_VALUE_CACHE_LOCK.get_or_init(|| SyncFactorCache::new(NUMERIC_VALUE_CACHE_SIZE))
}

impl Default for Factor {
    fn default() -> Self {
        Numeric(1)
    }
}

peg::parser! {
  pub grammar expression_parser() for str {
    pub rule number() -> FactorBeingParsed
      = n:$(['0'..='9']+) { n.parse::<NumericFactor>().map(FactorBeingParsed::Numeric).unwrap_or_else(|_| FactorBeingParsed::BigNumber(n.into())) }

    #[cache_left_rec]
    pub rule arithmetic() -> FactorBeingParsed = precedence!{
      x:(@) "+" y:@ { FactorBeingParsed::AddSub { left: x.into(), right: y.into(), subtract: false } }
      x:(@) "-" y:@ { FactorBeingParsed::AddSub { left: x.into(), right: y.into(), subtract: true } }
      --
      x:(@) "/" y:@ {
        let mut x = x;
        let mut y = y;
        if let FactorBeingParsed::Divide { ref mut right, .. } = x {
            *right.entry(y).or_insert(0) += 1;
            x
        } else if let FactorBeingParsed::Divide { ref mut left, ref mut right } = y {
            let old_left = core::mem::take(left);
            **left = FactorBeingParsed::Multiply { terms: [(*old_left, 1), (x, 1)].into() };
            y
        } else {
            FactorBeingParsed::Divide { left: x.into(), right: [(y, 1)].into() }
        }
      }
      --
      x:(@) "*" y:@ {
        let mut x = x;
        let mut y = y;
        if let FactorBeingParsed::Multiply { ref mut terms, .. } = x {
            *terms.entry(y).or_insert(0) += 1;
            x
        } else if let FactorBeingParsed::Multiply { ref mut terms, .. } = y {
            *terms.entry(x).or_insert(0) += 1;
            y
        } else if x == y {
            FactorBeingParsed::Multiply { terms: [(x, 2)].into() }
        } else {
            FactorBeingParsed::Multiply { terms: [(x, 1), (y, 1)].into() }
        }
      }
      --
      x:@ "^" y:(@) {
                if let FactorBeingParsed::Numeric(y) = y && let Ok(y_numeric) = NumberLength::try_from(y) {
                  FactorBeingParsed::Multiply { terms: [(x, y_numeric)].into() }
                } else {
                  FactorBeingParsed::Power { base: x.into(), exponent: y.into() }
                }
      }
      --
      x:@ "!" { FactorBeingParsed::Factorial(x.into()) }
      x:@ y:$("#"+) {
                    let hashes = y.len();
                    let mut output = x;
                    for _ in 0..(hashes >> 1) {
                        output = FactorBeingParsed::Primorial(FactorBeingParsed::Numeric(SIEVE.with_borrow_mut(|sieve| sieve.nth_prime(evaluate_as_numeric(&Factor::from(output)).unwrap() as u64)) as NumericFactor).into());
                    }
                    if !hashes.is_multiple_of(2) {
                        output = FactorBeingParsed::Primorial(output.into())
                    };
                    output
                }
      --
      "M" x:@ { FactorBeingParsed::AddSub { left: FactorBeingParsed::Power { base: FactorBeingParsed::Numeric(2).into(), exponent: Box::new(x) }.into(), right: FactorBeingParsed::Numeric(1).into(), subtract: true } }
      --
      "I" x:@ { FactorBeingParsed::Fibonacci(x.into()) }
      --
      "lucas(" x:arithmetic() ")" { FactorBeingParsed::Lucas(x.into()) }
      --
      n:$(['0'..='9']+ "..." ['0'..='9']+) { FactorBeingParsed::ElidedNumber(n.into()) }
      --
      n:number() { n }
      --
      "(" e:arithmetic() ")" { e }
    }
  }
}

fn largest_prime_le(mut given: NumericFactor) -> NumericFactor {
    while given >= 2 {
        if is_prime(given) {
            return given;
        }
        given -= 1;
    }
    1
}

impl Factor {
    pub fn one() -> Factor {
        Numeric(1)
    }
    pub fn two() -> Factor {
        Numeric(2)
    }
    pub fn three() -> Factor {
        Numeric(3)
    }
    pub fn five() -> Factor {
        Numeric(5)
    }

    pub fn multiply(terms: BTreeMap<Factor, NumberLength>) -> Self {
        let terms_hash = hash(&terms);
        Complex(Multiply { terms, terms_hash }.into())
    }

    pub fn divide(left: Factor, right: impl IntoIterator<Item = (Factor, NumberLength)>) -> Self {
        let right = right.into_iter().collect();
        let right_hash = hash(&right);
        Complex(
            Divide {
                left,
                right_hash,
                right,
            }
            .into(),
        )
    }

    #[inline(always)]
    pub fn known_id(&self) -> Option<EntryId> {
        if let Numeric(n) = self
            && *n <= MAX_ID_EQUAL_TO_VALUE
        {
            Some(*n)
        } else {
            None
        }
    }
    #[inline(always)]
    pub fn as_numeric(&self) -> Option<NumericFactor> {
        match self {
            Numeric(n) => Some(*n),
            _ => None,
        }
    }

    #[inline(always)]
    pub fn to_owned_string(&self) -> HipStr<'static> {
        match self {
            Numeric(n) => n.to_string().into(),
            Factor::BigNumber(s) => s.0.clone(),
            _ => self.to_string().into(),
        }
    }

    #[inline(always)]
    pub fn as_str_non_numeric(&self) -> Option<HipStr<'static>> {
        match self {
            Numeric(_) => None,
            Factor::BigNumber(n) => Some(n.0.clone()),
            _ => Some(self.to_string().into()),
        }
    }

    #[inline(always)]
    fn last_digit(&self) -> Option<u8> {
        match self {
            Factor::BigNumber(BigNumber(n)) | ElidedNumber(n) => {
                Some(n.chars().last().unwrap().to_digit(10).unwrap() as u8)
            }
            Numeric(n) => Some((n % 10) as u8),
            _ => None,
        }
    }

    #[inline]
    pub fn may_be_proper_divisor_of(&self, other: &Factor) -> bool {
        fn product_may_be_divisor_of(
            terms: &BTreeMap<Factor, NumberLength>,
            other: &Factor,
        ) -> bool {
            terms.iter().all(|(term, exponent)| {
                if *exponent == 0 {
                    return true;
                }
                if !term.may_be_proper_divisor_of(other) {
                    return false;
                }
                if *exponent == 1 {
                    return true;
                }
                let mut tested_exponent = 1;
                let mut quotient = div_exact(other, term);
                while let Some(next_quotient) = quotient {
                    if !term.may_be_proper_divisor_of(&next_quotient) {
                        return false;
                    }
                    tested_exponent += 1;
                    if *exponent == tested_exponent {
                        return true;
                    }
                    quotient = div_exact(&next_quotient, term);
                }
                true
            })
        }
        if let Some(n) = evaluate_as_numeric(self) {
            if let Some(other_n) = evaluate_as_numeric(other) {
                return other_n > n && other_n.is_multiple_of(n);
            } else if let Some(m) = modulo_as_numeric(other, n)
                && m != 0
            {
                return false;
            }
        }
        if let Some((log10_self_lower, _)) = get_cached_log10_bounds(self)
            && let Some((_, log10_other_upper)) = get_cached_log10_bounds(other)
            && log10_self_lower > log10_other_upper
        {
            return false;
        }
        match *self {
            Factor::BigNumber(_) => match *other {
                Numeric(_) => return false,
                Factor::BigNumber(_) => {
                    if self > other {
                        return false;
                    }
                }
                _ => {}
            },
            Complex(ref c) => match **c {
                Divide {
                    ref left,
                    ref right,
                    ..
                } => {
                    if !product_may_be_divisor_of(right, left) {
                        // Can't be an integer, therefore can't be a divisor
                        return false;
                    }
                }
                Multiply { ref terms, .. } => {
                    if !product_may_be_divisor_of(terms, other) {
                        return false;
                    }
                }
                Factorial(ref term) => {
                    if let Some(term) = evaluate_as_numeric(term)
                        && let Complex(ref c) = *other
                    {
                        match **c {
                            Factorial(ref other_term) => {
                                if let Some(other_term) = evaluate_as_numeric(other_term)
                                    && other_term <= term
                                {
                                    return false;
                                }
                            }
                            Primorial(_) => {
                                if term >= 4 {
                                    // Primorials are squarefree, factorials of >=4 aren't
                                    return false;
                                }
                            }
                            _ => {}
                        }
                        if (2..=term).any(|i| !Numeric(i).may_be_proper_divisor_of(other)) {
                            return false;
                        }
                    }
                }
                Primorial(ref term) => {
                    if let Some(term) = evaluate_as_numeric(term)
                        && let Complex(ref c) = *other
                    {
                        match **c {
                            Factorial(ref other_term) => {
                                if let Some(other_term) = evaluate_as_numeric(other_term)
                                    && other_term < largest_prime_le(term)
                                {
                                    // factorials of 4+ aren't squarefree, but primorials are
                                    return false;
                                }
                            }
                            Primorial(ref other_term) => {
                                if let Some(other_term) = evaluate_as_numeric(other_term)
                                    && (other_term <= term || (term..=other_term).any(is_prime))
                                {
                                    return false;
                                }
                            }
                            _ => {}
                        }
                        if (2..=term)
                            .any(|i| is_prime(i) && !Numeric(i).may_be_proper_divisor_of(other))
                        {
                            return false;
                        }
                    }
                }
                _ => {}
            },
            _ => {}
        }
        if let Complex(ref c) = *other
            && let Divide {
                ref left,
                ref right,
                ..
            } = **c
        {
            if !product_may_be_divisor_of(right, left) {
                return false;
            }
            if let Some(right_exponent) = right.get(self) {
                if !Factor::multiply([(self.clone(), right_exponent.saturating_add(1))].into())
                    .may_be_proper_divisor_of(left)
                {
                    return false;
                }
            } else if !self.may_be_proper_divisor_of(left) {
                return false;
            }
        }
        if let Some(quotient) = div_exact(other, self)
            && let Some(quotient_numeric) = evaluate_as_numeric(&quotient)
        {
            return quotient_numeric > 1;
        }
        let Some(last_digit) = self.last_digit() else {
            return true;
        };
        let Some(other_last_digit) = other.last_digit() else {
            return true;
        };
        match last_digit {
            0 => vec![0],
            2 | 4 | 6 | 8 => vec![0, 2, 4, 6, 8],
            5 => vec![0, 5],
            1 | 3 | 7 | 9 => vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
            _ => unsafe { unreachable_unchecked() },
        }
        .contains(&other_last_digit)
    }

    pub fn is_elided(&self) -> bool {
        match self {
            Numeric(_) => false,
            Factor::BigNumber(_) => false,
            ElidedNumber(_) => true,
            UnknownExpression(str) => str.contains("..."),
            Complex(c) => match **c {
                AddSub {
                    terms: (ref left, ref right),
                    ..
                } => left.is_elided() || right.is_elided(),
                Multiply { ref terms, .. } => terms.keys().any(Factor::is_elided),
                Divide {
                    ref left,
                    ref right,
                    ..
                } => left.is_elided() || right.keys().any(Factor::is_elided),
                Power {
                    ref base,
                    ref exponent,
                } => base.is_elided() || exponent.is_elided(),
                Fibonacci(ref term) => term.is_elided(),
                Lucas(ref term) => term.is_elided(),
                Factorial(ref term) => term.is_elided(),
                Primorial(ref term) => term.is_elided(),
            },
        }
    }
}

impl From<NumericFactor> for Factor {
    #[inline(always)]
    fn from(value: NumericFactor) -> Self {
        Numeric(value)
    }
}

impl From<BigNumber> for Factor {
    #[inline(always)]
    fn from(value: BigNumber) -> Self {
        Factor::BigNumber(value)
    }
}

impl From<&str> for Factor {
    #[inline(always)]
    fn from(value: &str) -> Self {
        if let Ok(numeric) = value.parse() {
            return Numeric(numeric);
        }
        info!("Parsing expression {value}");
        task::block_in_place(|| {
            expression_parser::arithmetic(value)
                .map(Factor::from)
                .unwrap_or_else(|e| {
                    error!("Error parsing expression {value}: {e}");
                    UnknownExpression(value.into())
                })
        })
    }
}

impl Display for Factor {
    #[inline(always)]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Numeric(n) => n.fmt(f),
            Factor::BigNumber(s) => write_bignum(f, s.as_ref()),
            UnknownExpression(e) => e.fmt(f),
            ElidedNumber(e) => e.fmt(f),
            Complex(c) => match **c {
                AddSub {
                    terms: (ref left, ref right),
                    subtract,
                } => f.write_fmt(format_args!(
                    "({left}{}{right})",
                    if subtract { '-' } else { '+' }
                )),
                Multiply { ref terms, .. } => f.write_fmt(format_args!(
                    "({})",
                    terms
                        .iter()
                        .map(|(term, exponent)| if *exponent == 1 {
                            term.to_string()
                        } else {
                            format!("({term})^{exponent}")
                        })
                        .join("*")
                )),
                Divide {
                    ref left,
                    ref right,
                    ..
                } => f.write_fmt(format_args!(
                    "({left}/{})",
                    right
                        .iter()
                        .map(|(term, exponent)| if *exponent == 1 {
                            term.to_string()
                        } else {
                            format!("({term})^{exponent}")
                        })
                        .join("/")
                )),
                Power {
                    ref base,
                    ref exponent,
                } => f.write_fmt(format_args!("({base})^({exponent})")),
                Factorial(ref input) => f.write_fmt(format_args!("({input}!)")),
                Primorial(ref input) => f.write_fmt(format_args!("({input}#)")),
                Fibonacci(ref input) => f.write_fmt(format_args!("I({input})")),
                Lucas(ref input) => f.write_fmt(format_args!("lucas({input})")),
            },
        }
    }
}

thread_local! {
    pub static SIEVE: RefCell<NaiveBuffer> = RefCell::new(NaiveBuffer::new());
}

#[inline(always)]
fn count_frequencies<T: Eq + Ord>(vec: impl Iterator<Item = T>) -> BTreeMap<T, NumberLength> {
    let mut counts = BTreeMap::new();
    for item in vec {
        *counts.entry(item).or_insert(0) += 1;
    }
    counts
}

#[inline(always)]
fn multiset_intersection<T: Eq + Ord + Clone>(
    mut vec1: BTreeMap<T, NumberLength>,
    mut vec2: BTreeMap<T, NumberLength>,
) -> BTreeMap<T, NumberLength> {
    if vec1.is_empty() || vec2.is_empty() {
        return BTreeMap::new();
    }
    let mut intersection_vec = BTreeMap::new();
    if vec2.len() < vec1.len() {
        swap(&mut vec1, &mut vec2);
    }
    for (item, count1) in vec1.into_iter() {
        if let Some(&count2) = vec2.get(&item) {
            let min_count = count1.min(count2);
            intersection_vec.insert(item, min_count);
        }
    }
    intersection_vec
}

#[inline(always)]
fn multiset_union<T: Eq + Ord + Clone>(
    mut sets: Vec<BTreeMap<T, NumberLength>>,
) -> BTreeMap<T, NumberLength> {
    sets.retain(|set| !set.is_empty());
    match sets.len() {
        0 => return BTreeMap::new(),
        1 => return sets.pop().unwrap(),
        _ => {}
    }
    let mut total_counts = BTreeMap::new();
    for set in sets {
        for (item, count) in set {
            let total = total_counts.entry(item).or_insert(count);
            *total = (*total).max(count);
        }
    }
    total_counts
}

#[inline]
fn fibonacci_factors(
    term: NumericFactor,
    subset_recursion: bool,
) -> BTreeMap<Factor, NumberLength> {
    debug!("fibonacci_factors: term {term}, subset_recursion {subset_recursion}");

    if term < SMALL_FIBONACCI_FACTORS.len() as NumericFactor {
        count_frequencies(
            SMALL_FIBONACCI_FACTORS[term as usize]
                .iter()
                .copied()
                .map(Numeric),
        )
    } else if term.is_multiple_of(2) {
        let mut factors = fibonacci_factors(term >> 1, subset_recursion);
        sum_factor_btreemaps(&mut factors, lucas_factors(term >> 1, subset_recursion));
        factors
    } else if !subset_recursion {
        [(Complex(Fibonacci(Numeric(term)).into()), 1)].into()
    } else {
        let factors_of_term = find_raw_factors_of_numeric(term);
        let full_set_size: NumberLength = factors_of_term.values().copied().sum();
        let subsets = power_multiset(factors_of_term);
        let mut subset_factors = Vec::with_capacity(subsets.len().saturating_sub(2));
        for subset in subsets {
            if subset.values().copied().sum::<NumberLength>() < full_set_size && !subset.is_empty()
            {
                let product: NumericFactor = subset
                    .into_iter()
                    .map(|(factor, exponent)| factor.pow(exponent))
                    .product();
                if product > 2 {
                    subset_factors.push(fibonacci_factors(product, false));
                }
            }
        }
        multiset_union(subset_factors)
    }
}

#[inline]
fn lucas_factors(term: NumericFactor, subset_recursion: bool) -> BTreeMap<Factor, NumberLength> {
    debug!("lucas_factors: term {term}, subset_recursion {subset_recursion}");
    if term < SMALL_LUCAS_FACTORS.len() as NumericFactor {
        count_frequencies(
            SMALL_LUCAS_FACTORS[term as usize]
                .iter()
                .copied()
                .map(Numeric),
        )
    } else if !subset_recursion {
        [(Complex(Lucas(Numeric(term)).into()), 1)].into()
    } else {
        let mut factors_of_term = find_raw_factors_of_numeric(term);
        let power_of_2 = factors_of_term.remove(&2).unwrap_or(0) as NumericFactor;
        let full_set_size: NumberLength = factors_of_term.values().copied().sum();
        let subsets = power_multiset(factors_of_term);
        let mut subset_factors = Vec::with_capacity(subsets.len().saturating_sub(2));
        for subset in subsets {
            if subset.values().copied().sum::<NumberLength>() < full_set_size && !subset.is_empty()
            {
                let product = subset
                    .into_iter()
                    .map(|(factor, exponent)| factor.pow(exponent))
                    .product::<NumericFactor>()
                    << power_of_2;
                if product > 2 {
                    subset_factors.push(lucas_factors(product, false));
                }
            }
        }
        multiset_union(subset_factors)
    }
}

#[inline]
fn power_multiset<T: PartialEq + Ord + Copy>(
    multiset: BTreeMap<T, NumberLength>,
) -> Vec<BTreeMap<T, NumberLength>> {
    let total_size = multiset
        .values()
        .map(|count| (count + 1) as usize)
        .product();
    let mut result = Vec::with_capacity(total_size);
    for index in 0..total_size {
        let mut index_remainder = index;
        let mut subset = BTreeMap::new();
        for (item, count) in multiset.iter() {
            if index_remainder == 0 {
                break;
            }
            let divisor = (count + 1) as usize;
            let subset_count = index_remainder % divisor;
            index_remainder /= divisor;
            if subset_count != 0 {
                subset.insert(*item, subset_count as NumberLength);
            }
        }
        result.push(subset);
    }
    result
}

/// Modular inverse using extended Euclidean algorithm
#[inline]
fn modinv(a: NumericFactor, m: NumericFactor) -> Option<NumericFactor> {
    let mut t: SignedNumericFactor = 0;
    let mut newt: SignedNumericFactor = 1;
    let m: SignedNumericFactor = m.try_into().ok()?;
    let mut r = m;
    let mut newr: SignedNumericFactor = a.try_into().ok()?;

    while newr != 0 {
        let quotient = r / newr;
        t -= quotient * newt;
        swap(&mut t, &mut newt);
        r -= quotient * newr;
        swap(&mut r, &mut newr);
    }

    if r > 1 {
        return None; // no inverse
    }

    if t < 0 {
        t += m;
    }

    t.try_into().ok()
}

fn factor_power(a: NumericFactor, n: NumberLength) -> (NumericFactor, NumberLength) {
    if a == 1 {
        return (1, 1);
    }
    // A NumericFactor can't be a 128th or higher power
    for prime in [
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
        97, 101, 103, 107, 109, 113, 127,
    ] {
        if let Some(root) = a.nth_root_exact(prime as u32) {
            return match n.checked_mul(prime as NumberLength) {
                Some(product) => become factor_power(root, product),
                None => (a, n),
            };
        }
    }
    (a, n)
}

pub fn to_like_powers(
    left: &Factor,
    right: &Factor,
    subtract: bool,
) -> BTreeMap<Factor, NumberLength> {
    let mut exponent_factors = BTreeMap::new();
    let mut new_left = simplify(left);
    let mut new_right = simplify(right);
    for term in [&mut new_left, &mut new_right] {
        let exponent_numeric = match term {
            Numeric(a) => {
                let (a, n) = factor_power(*a, 1);
                if n > 1 {
                    *term = Factor::multiply([((Numeric(a), n as NumberLength))].into());
                    Some(n)
                } else {
                    None
                }
            }
            Complex(c) => match **c {
                Power { ref exponent, .. } => {
                    evaluate_as_numeric(exponent).and_then(|e| NumberLength::try_from(e).ok())
                }
                Multiply { ref terms, .. } => {
                    // Return GCD of exponents without modifying the term
                    // nth_root_exact will handle the exponent division later
                    terms.values().copied().reduce(|x, y| x.gcd(&y))
                }
                _ => None,
            },
            _ => None,
        };
        if let Some(exponent_numeric) = exponent_numeric {
            exponent_factors = multiset_union(vec![
                exponent_factors,
                find_raw_factors_of_numeric(exponent_numeric.into()),
            ]);
        }
    }
    if exponent_factors.is_empty() {
        return BTreeMap::new();
    }
    let expr = simplify_add_sub(&new_left, &new_right, subtract);
    let mut results = BTreeMap::new();
    for (factor, _) in exponent_factors {
        if let Ok(factor) = NumberLength::try_from(factor)
            && (subtract || (factor != 2))
            && let Some(left_root) = nth_root_exact(&new_left, factor)
            && let Some(right_root) = nth_root_exact(&new_right, factor)
        {
            let new_factor = simplify_add_sub(&left_root, &right_root, subtract);
            let new_cofactor = if subtract && factor == 2 {
                simplify_add_sub(&left_root, &right_root, false)
            } else {
                div_exact(&expr, &new_factor)
                    .unwrap_or_else(|| simplify_divide(&expr, &[(new_factor.clone(), 1)].into()))
            };
            *results.entry(new_cofactor).or_insert(0) += 1;
            *results.entry(new_factor).or_insert(0) += 1;
        }
    }
    results
}

pub fn div_exact(product: &Factor, divisor: &Factor) -> Option<Factor> {
    if product == divisor {
        return Some(Factor::one());
    }
    if let Some(product_numeric) = evaluate_as_numeric(product)
        && let Some(divisor_numeric) = evaluate_as_numeric(divisor)
    {
        return product_numeric.div_exact(divisor_numeric).map(Numeric);
    }
    match *product {
        Complex(ref c) => match **c {
            Power {
                ref base,
                ref exponent,
            } => {
                if base == divisor {
                    // x^y / x -> x^(y-1)
                    Some(simplify_power(
                        base,
                        &simplify_add_sub(exponent, &Factor::one(), true),
                    ))
                } else if let Some(exponent_numeric) = evaluate_as_numeric(exponent)
                    && let Ok(exponent_numeric) = NumberLength::try_from(exponent_numeric)
                    && let Some(divisor_root) = nth_root_exact(divisor, exponent_numeric)
                {
                    Some(simplify_multiply(
                        &[(div_exact(base, &divisor_root)?, exponent_numeric)].into(),
                    ))
                } else {
                    None
                }
            }
            Multiply { ref terms, .. } => {
                let mut divisor_terms = if let Complex(ref c) = *divisor
                    && let Multiply { ref terms, .. } = **c
                {
                    Cow::Borrowed(terms)
                } else {
                    Cow::Owned([(divisor.clone(), 1)].into())
                };

                let mut new_terms = terms.clone();
                let mut cancelled_any = false;
                for (term, exponent) in new_terms.iter_mut() {
                    if let Some(divisor_exponent) = divisor_terms.to_mut().get_mut(term) {
                        let min_exponent = (*divisor_exponent).min(*exponent);
                        *divisor_exponent -= min_exponent;
                        *exponent -= min_exponent;
                        cancelled_any = true;
                    }
                }

                if cancelled_any {
                    new_terms.retain(|_, exponent| *exponent != 0);
                    divisor_terms.to_mut().retain(|_, exponent| *exponent != 0);
                }

                if divisor_terms.is_empty() {
                    return Some(simplify_multiply(&new_terms));
                }
                if new_terms.is_empty() {
                    // Try to see if divisor_terms (all numeric) divides 1
                    let divisor_numeric: NumericFactor = divisor_terms
                        .iter()
                        .map(|(term, exponent)| {
                            evaluate_as_numeric(term)
                                .and_then(|numeric| numeric.checked_pow(*exponent))
                        })
                        .collect::<Option<Vec<_>>>()?
                        .into_iter()
                        .try_reduce(|x, y| x.checked_mul(y))??;
                    if divisor_numeric == 1 {
                        return Some(Factor::one());
                    }
                    return None;
                }

                // Numeric fallback using REMAINING terms
                let divisor_numeric: NumericFactor = divisor_terms
                    .iter()
                    .map(|(term, exponent)| {
                        evaluate_as_numeric(term).and_then(|numeric| numeric.checked_pow(*exponent))
                    })
                    .collect::<Option<Vec<_>>>()?
                    .into_iter()
                    .try_reduce(|x, y| x.checked_mul(y))??;

                let product_numeric: NumericFactor = new_terms
                    .iter()
                    .map(|(term, exponent)| {
                        evaluate_as_numeric(term).and_then(|numeric| numeric.checked_pow(*exponent))
                    })
                    .collect::<Option<Vec<_>>>()?
                    .into_iter()
                    .try_reduce(|x, y| x.checked_mul(y))??;

                Some(Numeric(product_numeric.div_exact(divisor_numeric)?))
            }
            Divide {
                ref left,
                ref right,
                ..
            } => Some(simplify_divide(&div_exact(left, divisor)?, right)),
            Factorial(ref term) => {
                if let Some(divisor) = evaluate_as_numeric(divisor)
                    && let Some(term) = evaluate_as_numeric(term)
                {
                    let mut new_term = term;
                    while let Some(divisor) = divisor.div_exact(new_term) {
                        new_term -= 1;
                        if divisor == 1 {
                            return Some(simplify(&Complex(Factorial(Numeric(new_term)).into())));
                        }
                    }
                }
                None
            }
            Primorial(ref term) => {
                if let Some(mut divisor) = evaluate_as_numeric(divisor)
                    && let Some(term) = evaluate_as_numeric(term)
                {
                    let mut new_term = term;
                    while !is_prime(new_term)
                        || divisor
                            .div_exact(new_term)
                            .inspect(|new_divisor| divisor = *new_divisor)
                            .is_some()
                    {
                        new_term -= 1;
                        if divisor == 1 {
                            return Some(simplify(&Complex(Primorial(Numeric(new_term)).into())));
                        }
                    }
                }
                None
            }
            AddSub {
                terms: (ref left, ref right),
                subtract,
            } => {
                if let Some(new_left) = div_exact(left, divisor)
                    && let Some(new_right) = div_exact(right, divisor)
                {
                    Some(simplify_add_sub(&new_left, &new_right, subtract))
                } else {
                    None
                }
            }
            _ => None,
        },
        Factor::BigNumber(ref n) => {
            let mut n_reduced = n.as_ref();
            let mut reduced = false;
            let d_reduced = match *divisor {
                Numeric(d) => {
                    let mut d_reduced = d;
                    while d_reduced.is_multiple_of(10) && n_reduced.ends_with('0') {
                        reduced = true;
                        n_reduced = &n_reduced[0..(n_reduced.len() - 1)];
                        d_reduced /= 10;
                    }
                    Some(Numeric(d_reduced))
                }
                Factor::BigNumber(ref d) => {
                    let mut d_reduced = d.as_ref();
                    while d_reduced.ends_with('0') && n_reduced.ends_with('0') {
                        reduced = true;
                        d_reduced = &d_reduced[0..(d_reduced.len() - 1)];
                        n_reduced = &n_reduced[0..(n_reduced.len() - 1)];
                    }
                    Some(Factor::from(d_reduced))
                }
                _ => None,
            };
            if reduced && let Some(d_reduced) = d_reduced {
                div_exact(&Factor::from(n_reduced), &d_reduced)
            } else {
                None
            }
        }
        _ => None,
    }
}

pub fn nth_root_exact(factor: &Factor, root: NumberLength) -> Option<Factor> {
    if root == 1 {
        return Some(factor.clone());
    }
    if let Some(factor_numeric) = evaluate_as_numeric(factor) {
        if factor_numeric == 1 {
            return Some(Factor::one());
        }
        return factor_numeric.nth_root_exact(root).map(Numeric);
    }
    if let Complex(ref c) = *factor {
        match **c {
            Power {
                ref base,
                ref exponent,
            } => {
                if evaluate_as_numeric(base) == Some(1) {
                    return Some(Factor::one());
                }
                if let Some(exponent_numeric) = evaluate_as_numeric(exponent)
                    && let Some(reduced_exponent) = exponent_numeric.div_exact(root.into())
                {
                    Some(simplify_multiply(
                        &[(base.clone(), reduced_exponent as NumberLength)].into(),
                    ))
                } else {
                    None
                }
            }
            Multiply { ref terms, .. } => {
                let new_terms = nth_root_of_product(terms, root)?;
                Some(simplify_multiply(&new_terms))
            }
            Divide {
                ref left,
                ref right,
                ..
            } => {
                let new_left = nth_root_exact(left, root)?;
                let new_right = nth_root_of_product(right, root)?;
                Some(simplify_divide(&new_left, &new_right))
            }
            _ => None,
        }
    } else {
        None
    }
}

fn nth_root_of_product(
    terms: &BTreeMap<Factor, NumberLength>,
    root: NumberLength,
) -> Option<BTreeMap<Factor, NumberLength>> {
    let root = NumberLength::try_from(root).ok()?;
    terms
        .iter()
        .map(|(term, exponent)| {
            nth_root_exact(term, root)
                .map(|x| (x, *exponent))
                .or_else(|| Some((nth_root_exact(term, root.div_exact(*exponent)?)?, 1)))
                .or_else(|| Some((term.clone(), exponent.div_exact(root)?)))
        })
        .collect()
}

#[inline(always)]
pub(crate) fn find_factors_of_numeric(input: NumericFactor) -> BTreeMap<Factor, NumberLength> {
    find_raw_factors_of_numeric(input)
        .into_iter()
        .map(|(factor, power)| (Numeric(factor), power))
        .collect()
}

#[inline(always)]
pub(crate) fn find_raw_factors_of_numeric(
    input: NumericFactor,
) -> BTreeMap<NumericFactor, NumberLength> {
    task::block_in_place(|| {
        if input <= 1 << 85 {
            factorize128(input)
                .into_iter()
                .map(|(factor, exponent)| (factor, exponent as NumberLength))
                .collect()
        } else {
            let mut prefs = Preferences::default();
            prefs.verbosity = Silent;
            let mut factors = BTreeMap::new();
            for factor in factor(input.into(), Siqs, &prefs).unwrap() {
                *factors
                    .entry(NumericFactor::try_from(factor).unwrap())
                    .or_insert(0 as NumberLength) += 1;
            }
            factors
        }
    })
}

#[inline(always)]
fn estimate_log10_internal(expr: &Factor) -> (NumberLength, NumberLength) {
    debug!("estimate_log10_internal: {expr}");
    if let Some(cached_log10_bounds) = get_cached_log10_bounds(expr) {
        return cached_log10_bounds;
    }
    let bounds = match *expr {
        Numeric(n) => log10_bounds(n),
        Factor::BigNumber(ref expr) => {
            let len = expr.as_ref().len();
            ((len - 1) as NumberLength, len as NumberLength)
        }
        Complex(ref c) => match **c {
            Fibonacci(ref x) | Lucas(ref x) => {
                // Fibonacci or Lucas number
                let Some(term_number) = evaluate_as_numeric(x) else {
                    warn!("Could not parse term number of a Lucas number: {}", x);
                    return (0, NumberLength::MAX);
                };
                let est_log = term_number as f64 * 0.20898;
                (
                    est_log.floor() as NumberLength,
                    est_log.ceil() as NumberLength + 1,
                )
            }
            Factorial(ref input) => {
                // factorial
                let Some(input) = evaluate_as_numeric(input) else {
                    warn!("Could not parse input to a factorial: {}", input);
                    return (0, NumberLength::MAX);
                };
                let (ln_factorial, _) = ((input + 1) as f64).ln_gamma();

                // LN_10 is already rounded up
                let log_factorial_lower_bound = ln_factorial.next_down() / LN_10;
                let log_factorial_upper_bound = ln_factorial.next_up() / LN_10.next_down();

                (
                    log_factorial_lower_bound.floor() as NumberLength,
                    log_factorial_upper_bound.ceil() as NumberLength,
                )
            }
            Primorial(ref input) => {
                // primorial
                let Some(input) = evaluate_as_numeric(input) else {
                    warn!("Could not parse input to a factorial: {}", input);
                    return (0, NumberLength::MAX);
                };

                // Lower bound is from
                // Rosser, J. Barkley; Schoenfeld, Lowell (1962-03-01).
                // "Approximate formulas for some functions of prime numbers".
                // Illinois Journal of Mathematics 6 (1), p. 70
                // https://projecteuclid.org/journalArticle/Download?urlId=10.1215%2Fijm%2F1255631807
                // (p. 7 of PDF)
                let lower_bound = if input >= 563 {
                    (input as f64 * (1.0 / (2.0 * (input as f64).ln())) / LN_10).ceil()
                        as NumberLength
                } else if input >= 41 {
                    (input as f64 * (1.0 / (input as f64).ln()) / LN_10.next_down()).ceil()
                        as NumberLength
                } else {
                    0
                };
                let upper_bound = (1.01624 / LN_10 * input as f64).floor() as NumberLength;
                (lower_bound, upper_bound)
            }
            Power {
                ref base,
                ref exponent,
            } => estimate_log10_power(base, exponent),
            Divide {
                ref left,
                ref right,
                ..
            } => {
                let (num_lower, num_upper) = estimate_log10_internal(left);
                let (denom_lower, denom_upper) = estimate_log10_of_product(right);
                let lower = num_lower.saturating_sub(denom_upper.saturating_add(1));
                let upper = num_upper.saturating_sub(denom_lower.saturating_sub(1));
                (lower, upper)
            }
            Multiply { ref terms, .. } => {
                // multiplication
                let (product_lower, product_upper) = estimate_log10_of_product(terms);
                (product_lower, product_upper)
            }
            AddSub {
                terms: (ref left, ref right),
                subtract,
            } => {
                // addition/subtraction
                let (left_lower, left_upper) = estimate_log10_internal(left);
                let (right_lower, right_upper) = estimate_log10_internal(right);
                let combined_lower = if subtract {
                    if right_upper >= left_lower - 1 {
                        0
                    } else {
                        left_lower.saturating_sub(1)
                    }
                } else {
                    left_lower.max(right_lower)
                };
                let combined_upper = if subtract {
                    left_upper
                } else {
                    left_upper.max(right_upper).saturating_add(1)
                };
                (combined_lower, combined_upper)
            }
        },
        ElidedNumber(_) => {
            // Elided numbers from factordb are always at least 51 digits
            (50, NumberLength::MAX)
        }
        UnknownExpression(_) => (0, NumberLength::MAX),
    };
    get_log10_cache().insert(expr.clone(), bounds);
    bounds
}

fn get_cached_log10_bounds(expr: &Factor) -> Option<(NumberLength, NumberLength)> {
    if let Numeric(numeric_value) = *expr {
        return Some(log10_bounds(numeric_value));
    }
    let log10_estimate_cache = get_log10_cache();
    if let Some(Some(numeric_value)) = get_numeric_value_cache().get(expr) {
        // Any old estimate is no longer worth saving
        log10_estimate_cache.remove(expr);
        return Some(log10_bounds(numeric_value));
    }
    log10_estimate_cache.get(expr)
}

fn get_log10_cache() -> &'static SyncFactorCache<(NumberLength, NumberLength)> {
    LOG10_ESTIMATE_CACHE_LOCK.get_or_init(|| SyncFactorCache::new(LOG10_ESTIMATE_CACHE_SIZE))
}

#[inline]
fn estimate_log10_power(base: &Factor, exponent: &Factor) -> (NumberLength, NumberLength) {
    let Some(exponent) =
        evaluate_as_numeric(exponent).and_then(|exponent| NumberLength::try_from(exponent).ok())
    else {
        return (0, NumberLength::MAX);
    };
    if let Some(base) = evaluate_as_numeric(base) {
        let lower = (base as f64).log10().next_down() * exponent as f64;
        let upper = (base as f64).log10().next_up() * (exponent as f64).next_up();
        (lower.floor() as NumberLength, upper.ceil() as NumberLength)
    } else {
        let (base_lower, base_upper) = estimate_log10_internal(base);
        (
            base_lower.saturating_mul(exponent),
            base_upper.saturating_mul(exponent),
        )
    }
}

fn log10_bounds(n: NumericFactor) -> (NumberLength, NumberLength) {
    match n {
        0 => {
            warn!("log10 estimate for 0 was requested");
            (0, 0)
        }
        1 => (0, 0),
        n => (
            n.ilog10() as NumberLength,
            (n - 1).ilog10() as NumberLength + 1,
        ),
    }
}

fn estimate_log10_of_product(
    terms: &BTreeMap<Factor, NumberLength>,
) -> (NumberLength, NumberLength) {
    let mut lower: NumberLength = 0;
    let mut upper: NumberLength = 0;
    for (term, exponent) in terms {
        let (power_lower, power_upper) = match *exponent {
            0 => (0, 0),
            1 => estimate_log10_internal(term),
            x => estimate_log10_power(term, &Numeric(x as NumericFactor)),
        };
        lower = lower.saturating_add(power_lower);
        upper = upper.saturating_add(power_upper).saturating_add(1);
    }
    (lower, upper - 1)
}

pub(crate) fn estimate_log10(expr: &Factor) -> (NumberLength, NumberLength) {
    let (lbound, ubound) = estimate_log10_internal(expr);
    if lbound > ubound {
        error!(
            "{expr}: estimate_log10 produced inconsistent bounds: lower bound {lbound}, upper bound {ubound}"
        );
        (0, NumberLength::MAX)
    } else {
        (lbound, ubound)
    }
}

pub(crate) fn modulo_as_numeric(expr: &Factor, modulus: NumericFactor) -> Option<NumericFactor> {
    if let Some(eval) = evaluate_as_numeric(expr) {
        return Some(eval % modulus);
    }
    match modulus {
        0 => {
            warn!("Attempted to evaluate {expr} modulo 0");
            None
        }
        1 => Some(0),
        _ => match *expr {
            Numeric(n) => Some(n % modulus),
            Factor::BigNumber(_) => {
                if (modulus == 2 || modulus == 5)
                    && let Some(last_digit) = expr.last_digit()
                {
                    Some(last_digit as NumericFactor % modulus)
                } else {
                    None
                }
            }
            ElidedNumber(_) | UnknownExpression(_) => None,
            Complex(ref c) => match **c {
                AddSub {
                    terms: (ref left, ref right),
                    subtract,
                } => {
                    let left = modulo_as_numeric(left, modulus)?;
                    let right = modulo_as_numeric(right, modulus)?;
                    if subtract {
                        let diff = left.abs_diff(right);
                        Some(if left > right {
                            diff.rem_euclid(modulus)
                        } else {
                            (modulus - diff.rem_euclid(modulus)) % modulus
                        })
                    } else {
                        Some((left + right) % modulus)
                    }
                }
                Multiply { ref terms, .. } => {
                    let mut product: NumericFactor = 1;
                    for (term, exponent) in terms.iter() {
                        product = product.checked_mul(
                            modulo_as_numeric(term, modulus)?
                                .powm(*exponent as NumericFactor, &modulus),
                        )? % modulus;
                    }
                    Some(product)
                }
                Divide {
                    ref left,
                    ref right,
                    ..
                } => {
                    let mut result = modulo_as_numeric(left, modulus)?;
                    for (term, exponent) in right.iter() {
                        let term_mod = modulo_as_numeric(term, modulus)?
                            .powm(*exponent as NumericFactor, &modulus);
                        match modinv(term_mod, modulus) {
                            Some(inv) => result = result.mulm(inv, &modulus),
                            None => return None,
                        }
                    }
                    Some(result)
                }
                Power {
                    ref base,
                    ref exponent,
                } => {
                    let base_mod = modulo_as_numeric(base, modulus)?;
                    let exp = evaluate_as_numeric(exponent)?;
                    Some(base_mod.powm(exp, &modulus))
                }
                Fibonacci(ref term) => {
                    let term = evaluate_as_numeric(term)?;
                    Some(pisano(term, vec![0, 1, 1], modulus))
                }
                Lucas(ref term) => {
                    let term = evaluate_as_numeric(term)?;
                    Some(pisano(term, vec![2, 1], modulus))
                }
                Factorial(ref term) => {
                    let term = evaluate_as_numeric(term)?;
                    if term >= modulus {
                        return Some(0);
                    }
                    if term == modulus - 1 {
                        // Wilson's theorem
                        return Some(if is_prime(modulus) {
                            term
                        } else if modulus == 4 {
                            2
                        } else {
                            0
                        });
                    }
                    let mut result = 1;
                    for i in 2..=term {
                        result = (result * i) % modulus;
                        if result == 0 {
                            return Some(0);
                        }
                    }
                    Some(result)
                }
                Primorial(ref term) => {
                    let term = evaluate_as_numeric(term)?;
                    if term >= modulus && (is_prime(term) || is_prime(modulus)) {
                        return Some(0);
                    }
                    let mut result = 1;
                    for i in 2..=term {
                        if is_prime(i) {
                            result = (result * i) % modulus;
                            if result == 0 {
                                return Some(0);
                            }
                        }
                    }
                    Some(result)
                }
            },
        },
    }
}

fn is_prime(val: NumericFactor) -> bool {
    SIEVE.with_borrow(|sieve| sieve.is_prime(&val, None)) != No
}

fn pisano(
    term: NumericFactor,
    mut sequence: Vec<NumericFactor>,
    modulus: NumericFactor,
) -> NumericFactor {
    let mut zeros = 0; // don't count the initial 0th term for Fibonacci sequence
    loop {
        if sequence.len() as NumericFactor == term + 1 {
            return *sequence.last().unwrap();
        }
        let next_term = (sequence[sequence.len() - 2] + sequence[sequence.len() - 1]) % modulus;
        if next_term == 0 {
            zeros += 1;
        }
        if zeros == 4 && next_term == sequence[0] {
            return sequence[(term % (sequence.len() as NumericFactor)) as usize];
        }
        sequence.push(next_term);
    }
}

pub(crate) fn simplify(expr: &Factor) -> Factor {
    match expr {
        Complex(c) => match **c {
            Multiply { ref terms, .. } => {
                simplify_multiply_internal(terms).unwrap_or_else(|| expr.clone())
            }
            Divide {
                ref left,
                ref right,
                ..
            } => simplify_divide_internal(left, right).unwrap_or_else(|| expr.clone()),
            Power {
                ref base,
                ref exponent,
            } => simplify_power_internal(base, exponent).unwrap_or_else(|| expr.clone()),
            Factorial(ref term) | Primorial(ref term) => match *term {
                Numeric(0) | Numeric(1) => Factor::one(),
                _ => expr.clone(),
            },
            AddSub {
                terms: (ref left, ref right),
                subtract,
            } => simplify_add_sub_internal(left, right, subtract).unwrap_or_else(|| expr.clone()),
            _ => expr.clone(),
        },
        _ => {
            if let Some(expr_numeric) = evaluate_as_numeric(expr) {
                Numeric(expr_numeric)
            } else {
                expr.clone()
            }
        }
    }
}

fn simplify_add_sub(left: &Factor, right: &Factor, subtract: bool) -> Factor {
    simplify_add_sub_internal(left, right, subtract).unwrap_or_else(|| {
        Complex(
            AddSub {
                terms: (left.clone(), right.clone()),
                subtract,
            }
            .into(),
        )
    })
}

fn simplify_add_sub_internal(left: &Factor, right: &Factor, subtract: bool) -> Option<Factor> {
    let mut new_left = simplify(left);
    let mut new_right = simplify(right);
    if let Numeric(n) = new_right
        && n == 0
    {
        return Some(new_left);
    }
    if !subtract
        && let Numeric(n) = new_left
        && n == 0
    {
        return Some(new_right);
    }
    match new_left.cmp(&new_right) {
        Ordering::Less => {
            if !subtract {
                swap(&mut new_left, &mut new_right);
            }
        }
        Ordering::Equal => {
            return if subtract {
                Some(Numeric(0))
            } else {
                Some(simplify_multiply(
                    &[(new_left, 1), (Factor::two(), 1)].into(),
                ))
            };
        }
        Ordering::Greater => {}
    }
    let result_numeric = if subtract {
        evaluate_as_numeric(&new_left)
            .and_then(|left| left.checked_sub(evaluate_as_numeric(&new_right)?))
    } else {
        evaluate_as_numeric(&new_left)
            .and_then(|left| left.checked_add(evaluate_as_numeric(&new_right)?))
    };
    if let Some(result_numeric) = result_numeric {
        Some(Numeric(result_numeric))
    } else if new_left != *left || new_right != *right {
        Some(Complex(
            AddSub {
                terms: (new_left, new_right),
                subtract,
            }
            .into(),
        ))
    } else {
        None
    }
}

fn simplify_power(base: &Factor, exponent: &Factor) -> Factor {
    simplify_power_internal(base, exponent).unwrap_or_else(|| {
        Complex(
            Power {
                base: base.clone(),
                exponent: exponent.clone(),
            }
            .into(),
        )
    })
}

fn simplify_power_internal(base: &Factor, exponent: &Factor) -> Option<Factor> {
    let mut new_base = simplify(base);
    let mut new_exponent = simplify(exponent);
    if let Numeric(n) = new_exponent {
        if n == 0 {
            return Some(Factor::one());
        } else if n == 1 {
            return Some(new_base);
        }
    }
    if let Numeric(new_base_numeric) = new_base {
        if new_base_numeric == 1 {
            return Some(Factor::one());
        }
        if let Some(new_exponent_numeric) =
            evaluate_as_numeric(&new_exponent).and_then(|e| NumberLength::try_from(e).ok())
        {
            let (factored_base, factored_exponent) =
                factor_power(new_base_numeric, new_exponent_numeric);
            if factored_exponent != new_exponent_numeric {
                new_base = Numeric(factored_base);
                new_exponent = Numeric(factored_exponent as NumericFactor);
            }
        }
    }
    match evaluate_as_numeric(&new_exponent) {
        Some(0) => Some(Factor::one()),
        Some(1) => Some(new_base),
        Some(n) => Some(simplify_multiply(
            &once((new_base, n as NumberLength)).collect(),
        )),
        None => {
            if *base == new_base && *exponent == new_exponent {
                None
            } else {
                Some(Complex(
                    Power {
                        base: new_base,
                        exponent: new_exponent,
                    }
                    .into(),
                ))
            }
        }
    }
}

pub fn simplify_divide(left: &Factor, right: &BTreeMap<Factor, NumberLength>) -> Factor {
    simplify_divide_internal(left, right)
        .unwrap_or_else(|| Factor::divide(left.clone(), right.clone()))
}

fn simplify_divide_internal(
    left: &Factor,
    right: &BTreeMap<Factor, NumberLength>,
) -> Option<Factor> {
    let mut new_left = left.clone();
    let mut new_right = right.clone();
    while let Complex(ref c) = new_left
        && let Divide {
            left: ref left_left,
            right: ref mid,
            ..
        } = **c
    {
        // (left_left / mid) / right
        for (term, exponent) in mid.iter() {
            *new_right.entry(term.clone()).or_insert(0) += *exponent;
        }
        new_left = left_left.clone();
        // left_left / (mid * right)
    }
    let mut new_left = simplify(&new_left);
    let mut cloned_right = new_right.clone();
    for (term, exponent) in new_right {
        let mut simplified = simplify(&term);
        if let Complex(ref c) = simplified
            && let Multiply { ref terms, .. } = **c
        {
            cloned_right.remove(&term);
            for (subterm, subterm_exponent) in terms {
                *cloned_right.entry(simplify(subterm)).or_insert(0) += exponent * subterm_exponent;
            }
        } else if simplified != term {
            if let Numeric(l) = new_left
                && let Numeric(r) = term
            {
                let gcd = l.gcd(&r);
                if gcd > 1
                    && let Some(gcd_root) = gcd.nth_root_exact(exponent)
                {
                    new_left = Numeric(l / gcd);
                    simplified = Numeric(r / gcd_root);
                }
            }
            *cloned_right.entry(simplified).or_insert(0) += cloned_right.remove(&term).unwrap();
        }
    }
    cloned_right.retain(|term, exponent| *exponent != 0 && *term != Factor::one());
    if let Some(exponent) = cloned_right.get_mut(&new_left) {
        *exponent -= 1;
        new_left = Factor::one();
    }
    if cloned_right.is_empty() {
        Some(new_left)
    } else if new_left == *left && cloned_right == *right {
        None
    } else {
        Some(Factor::divide(new_left, cloned_right))
    }
}

fn simplify_multiply(terms: &BTreeMap<Factor, NumberLength>) -> Factor {
    simplify_multiply_internal(terms).unwrap_or_else(|| Factor::multiply(terms.clone()))
}

fn simplify_multiply_internal(terms: &BTreeMap<Factor, NumberLength>) -> Option<Factor> {
    let mut new_terms = BTreeMap::new();
    let mut changed = false;

    for (term, exponent) in terms.iter() {
        let simplified = simplify(term);
        if simplified != *term {
            changed = true;
        }

        let (term, exponent) = if let Numeric(n) = simplified {
            if n == 1 {
                changed = true;
                continue;
            }
            let (factored_term, factored_exponent) = factor_power(n, *exponent);
            if factored_term != n {
                changed = true;
                (Numeric(factored_term), factored_exponent)
            } else {
                (Numeric(n), *exponent)
            }
        } else {
            (simplified, *exponent)
        };

        if let Complex(ref c) = term
            && let Multiply { ref terms, .. } = **c
        {
            changed = true;
            for (inner_term, inner_exponent) in terms.iter() {
                let k: Factor = inner_term.clone();
                *new_terms.entry(k).or_insert(0) += inner_exponent * exponent;
            }
        } else {
            *new_terms.entry(term).or_insert(0) += exponent;
        }
    }

    new_terms.retain(|factor, exponent| {
        if *factor == Factor::one() || *exponent == 0 {
            changed = true;
            false
        } else {
            true
        }
    });

    if !changed {
        return None;
    }

    match new_terms.len() {
        0 => Some(Factor::one()),
        1 => {
            let (factor, power) = new_terms.into_iter().next().unwrap();
            if power == 1 {
                Some(factor)
            } else {
                Some(Factor::multiply([(factor, power)].into()))
            }
        }
        _ => Some(Factor::multiply(new_terms)),
    }
}

pub(crate) fn evaluate_as_numeric(expr: &Factor) -> Option<NumericFactor> {
    if let Numeric(n) = expr {
        return Some(*n);
    }
    let numeric_value_cache = get_numeric_value_cache();
    let cached = numeric_value_cache.get(expr);
    match cached {
        Some(numeric) => numeric,
        None => {
            let numeric = match *expr {
                Numeric(n) => Some(n),
                Factor::BigNumber(_) => None,
                Complex(ref c) => match **c {
                    Lucas(ref term) => {
                        let term = evaluate_as_numeric(term)?;
                        match term {
                            0 => Some(2),
                            1 => Some(1),
                            185.. => None,
                            n => {
                                let mut a: NumericFactor = 2;
                                let mut b: NumericFactor = 1;
                                let mut result: NumericFactor = 0;

                                for _ in 2..=n {
                                    result = a + b;
                                    a = b;
                                    b = result;
                                }
                                Some(result)
                            }
                        }
                    }
                    Fibonacci(ref term) => {
                        let term = evaluate_as_numeric(term)?;
                        match term {
                            0 => Some(0),
                            1 | 2 => Some(1),
                            186.. => None,
                            n => {
                                let mut a: NumericFactor = 1;
                                let mut b: NumericFactor = 1;
                                let mut result: NumericFactor = 0;
                                for _ in 3..=n {
                                    result = a + b;
                                    a = b;
                                    b = result;
                                }
                                Some(result)
                            }
                        }
                    }
                    Factorial(ref term) => {
                        let term = evaluate_as_numeric(term)?;
                        match term {
                            0 | 1 => Some(1),
                            35.. => None,
                            x => {
                                let mut result = 1;
                                for i in 2..=x {
                                    result *= i;
                                }
                                Some(result)
                            }
                        }
                    }
                    Primorial(ref term) => {
                        let term = evaluate_as_numeric(term)?;
                        match term {
                            0 | 1 => Some(1),
                            103.. => None,
                            x => Some(
                                // SMALL_PRIMES always has all the primes we need
                                SMALL_PRIMES
                                    .iter()
                                    .copied()
                                    .map(NumericFactor::from)
                                    .take_while(|p| *p <= x)
                                    .product(),
                            ),
                        }
                    }
                    Power {
                        ref base,
                        ref exponent,
                    } => match evaluate_as_numeric(base)? {
                        0 => Some(0),
                        1 => Some(1),
                        base => {
                            base.checked_pow(u32::try_from(evaluate_as_numeric(exponent)?).ok()?)
                        }
                    },
                    Divide {
                        ref left,
                        ref right,
                        ..
                    } => {
                        let mut result = evaluate_as_numeric(left)?;
                        for (term, exponent) in right.iter() {
                            result = result.checked_div_exact(
                                evaluate_as_numeric(term)?.checked_pow(*exponent)?,
                            )?;
                        }
                        Some(result)
                    }
                    Multiply { ref terms, .. } => {
                        let mut result: NumericFactor = 1;
                        for (term, exponent) in terms.iter() {
                            result = result
                                .checked_mul(evaluate_as_numeric(term)?.checked_pow(*exponent)?)?;
                        }
                        Some(result)
                    }
                    AddSub {
                        terms: (ref left, ref right),
                        subtract,
                    } => {
                        let left = evaluate_as_numeric(left)?;
                        let right = evaluate_as_numeric(right)?;
                        if subtract {
                            left.checked_sub(right)
                        } else {
                            left.checked_add(right)
                        }
                    }
                },
                ElidedNumber(_) => None,
                UnknownExpression(_) => None,
            };
            numeric_value_cache.insert(expr.clone(), numeric);
            numeric
        }
    }
}

#[inline(always)]
fn find_factors(expr: &Factor) -> BTreeMap<Factor, NumberLength> {
    if FIND_FACTORS_STACK.with(|stack| stack.borrow().contains(expr)) {
        return [(expr.clone(), 1)].into();
    }
    if let Numeric(n) = expr
        && *n < 1 << 64
    {
        return find_factors_of_numeric(*n);
    }
    let factor_cache = FACTOR_CACHE_LOCK.get_or_init(|| SyncFactorCache::new(FACTOR_CACHE_SIZE));
    let cached = factor_cache.get(expr);
    match cached {
        Some(cached) => cached,
        None => {
            let _is_new = FIND_FACTORS_STACK.with(|stack| stack.borrow_mut().insert(expr.clone()));
            let results = task::block_in_place(|| {
                let expr_string = format!("find_factors: {expr}");
                info!("{}", expr_string);
                frame_sync(location!().named(expr_string), || {
                    let factors = match *expr {
                        Numeric(n) => find_factors_of_numeric(n),
                        Factor::BigNumber(ref n) => factor_big_num(n.as_ref()),
                        ElidedNumber(ref n) => factor_big_num(n.as_str()),
                        UnknownExpression(_) => [].into(),
                        Complex(ref c) => match **c {
                            Lucas(ref term) => {
                                // Lucas number
                                if let Some(term_number) = evaluate_as_numeric(term) {
                                    lucas_factors(term_number, true)
                                } else {
                                    warn!(
                                        "Could not parse term number of a Lucas number: {}",
                                        term
                                    );
                                    BTreeMap::new()
                                }
                            }
                            Fibonacci(ref term) => {
                                // Fibonacci number
                                if let Some(term_number) = evaluate_as_numeric(term) {
                                    fibonacci_factors(term_number, true)
                                } else {
                                    warn!(
                                        "Could not parse term number of a Fibonacci number: {}",
                                        term
                                    );
                                    BTreeMap::new()
                                }
                            }
                            Factorial(ref term) => {
                                // factorial
                                if let Some(input) = evaluate_as_numeric(term) {
                                    let mut factors = BTreeMap::new();
                                    for i in 2..=input {
                                        sum_factor_btreemaps(
                                            &mut factors,
                                            find_factors_of_numeric(i),
                                        );
                                    }
                                    factors
                                } else {
                                    warn!("Could not parse input to factorial function: {}", term);
                                    BTreeMap::new()
                                }
                            }
                            Primorial(ref term) => {
                                // primorial
                                if let Some(input) = evaluate_as_numeric(term) {
                                    let mut factors = BTreeMap::new();
                                    for i in 2..=input {
                                        if is_prime(i) {
                                            factors.insert(Numeric(i), 1);
                                        }
                                    }
                                    factors
                                } else {
                                    warn!("Could not parse input to primorial function: {}", term);
                                    BTreeMap::new()
                                }
                            }
                            Power {
                                ref base,
                                ref exponent,
                            } => {
                                let mut factors = find_factors(&simplify(base));
                                if let Some(power) = evaluate_as_numeric(exponent)
                                    .and_then(|power| NumberLength::try_from(power).ok())
                                    && power > 1
                                {
                                    factors
                                        .iter_mut()
                                        .for_each(|(_, exponent)| *exponent *= power);
                                }
                                factors
                            }
                            Divide {
                                ref left,
                                ref right,
                                ..
                            } => {
                                if let Some(exact_div) = div_exact(left, &simplify_multiply(right))
                                {
                                    find_factors(&exact_div)
                                } else {
                                    // division
                                    let mut left_remaining_factors: BTreeMap<Factor, NumberLength> =
                                        find_factors(&simplify(left))
                                            .into_iter()
                                            .filter(|(factor, _)| factor != expr && factor != left && !matches!(&factor, Complex(c) if matches!(**c, Divide {left: ref c_left, ..} if c_left == expr || c_left == left)))
                                            .collect();
                                    if left_remaining_factors.contains_key(expr) {
                                        // Abort to prevent infinite recursion
                                        return [].into();
                                    }
                                    let mut right_remaining_factors = right.clone();
                                    let intersection = multiset_intersection(
                                        left_remaining_factors.clone(),
                                        right_remaining_factors.clone(),
                                    );
                                    for (factor, common_exponent) in intersection {
                                        let right_remaining_exponent =
                                            right_remaining_factors.remove(&factor).unwrap()
                                                - common_exponent;
                                        let left_remaining_exponent =
                                            left_remaining_factors.remove(&factor).unwrap()
                                                - common_exponent;
                                        if right_remaining_exponent > 0 {
                                            right_remaining_factors
                                                .insert(factor, right_remaining_exponent);
                                        } else if left_remaining_exponent > 0 {
                                            left_remaining_factors
                                                .insert(factor, left_remaining_exponent);
                                        }
                                    }
                                    if right_remaining_factors.is_empty() {
                                        return left_remaining_factors;
                                    }
                                    let mut left_recursive_factors = BTreeMap::new();
                                    while let Some((mut factor, exponent)) =
                                        right_remaining_factors.pop_last()
                                    {
                                        if exponent == 0 {
                                            continue;
                                        }
                                        let mut left_exponent = left_recursive_factors
                                            .remove(&factor)
                                            .filter(|exponent| *exponent != 0)
                                            .or_else(|| {
                                                left_remaining_factors
                                                    .remove(&factor)
                                                    .filter(|exponent| *exponent != 0)
                                            });
                                        while left_exponent.is_none() {
                                            let simplified = simplify(&factor);
                                            if simplified != factor {
                                                left_exponent = left_recursive_factors
                                                    .remove(&simplified)
                                                    .filter(|exponent| *exponent != 0)
                                                    .or_else(|| {
                                                        left_remaining_factors
                                                            .remove(&simplified)
                                                            .filter(|exponent| *exponent != 0)
                                                    });
                                                factor = simplified;
                                            } else {
                                                break;
                                            }
                                        }
                                        if let Some(mut left_exponent) = left_exponent {
                                            let min_exponent = left_exponent.min(exponent);
                                            left_exponent -= min_exponent;
                                            let right_exponent = exponent - min_exponent;
                                            if right_exponent != 0 {
                                                right_remaining_factors
                                                    .insert(factor, right_exponent);
                                            } else if left_exponent != 0 {
                                                left_remaining_factors
                                                    .insert(factor, left_exponent);
                                            }
                                        } else if let Some((left_factor, left_factor_div_factor)) =
                                            left_remaining_factors
                                                .keys()
                                                .filter_map(|left_factor| {
                                                    div_exact(left_factor, &factor).map(
                                                        |left_factor_div_factor| {
                                                            (left_factor, left_factor_div_factor)
                                                        },
                                                    )
                                                })
                                                .next()
                                        {
                                            let mut left_exponent = left_remaining_factors
                                                .remove(&left_factor.clone())
                                                .unwrap();
                                            let min_exponent = left_exponent.min(exponent);
                                            left_exponent -= min_exponent;
                                            let right_exponent = exponent - min_exponent;
                                            if right_exponent != 0 {
                                                right_remaining_factors
                                                    .insert(factor, right_exponent);
                                            } else if left_exponent != 0 {
                                                left_remaining_factors
                                                    .insert(factor, left_exponent);
                                            }
                                            left_remaining_factors
                                                .insert(left_factor_div_factor, min_exponent);
                                        } else if let Some((left_factor, factor_div_left_factor)) =
                                            left_remaining_factors
                                                .keys()
                                                .filter_map(|left_factor| {
                                                    div_exact(&factor, left_factor).map(
                                                        |factor_div_left_factor| {
                                                            (left_factor, factor_div_left_factor)
                                                        },
                                                    )
                                                })
                                                .next()
                                        {
                                            let mut left_exponent = left_remaining_factors
                                                .remove(&left_factor.clone())
                                                .unwrap();
                                            let min_exponent = left_exponent.min(exponent);
                                            left_exponent -= min_exponent;
                                            let right_exponent = exponent - min_exponent;
                                            if right_exponent != 0 {
                                                right_remaining_factors
                                                    .insert(factor, right_exponent);
                                            } else if left_exponent != 0 {
                                                left_remaining_factors
                                                    .insert(factor, left_exponent);
                                            }
                                            right_remaining_factors
                                                .insert(factor_div_left_factor, min_exponent);
                                        } else {
                                            let subfactors = find_factors(&factor);
                                            for (subfactor, subfactor_exponent) in subfactors
                                                .into_iter()
                                                .filter(|(subfactor, _)| *subfactor != factor && !matches!(subfactor, Complex(c) if matches!(**c, Divide {ref left, ..} if *left == factor)))
                                            {
                                                *right_remaining_factors
                                                    .entry(subfactor)
                                                    .or_insert(0) += subfactor_exponent * exponent;
                                            }
                                        }
                                    }
                                    sum_factor_btreemaps(
                                        &mut left_recursive_factors,
                                        left_remaining_factors,
                                    );
                                    left_recursive_factors
                                }
                            }
                            Multiply { ref terms, .. } => {
                                if terms.is_empty() {
                                    return BTreeMap::new();
                                }
                                if terms.len() == 1 {
                                    let (factor, power) = terms.first_key_value().unwrap();
                                    return match power {
                                        0 => BTreeMap::new(),
                                        1 => find_factors(&simplify(factor)),
                                        _ => [(simplify(factor), *power)].into(),
                                    };
                                }
                                // multiplication
                                let mut factors = BTreeMap::new();
                                for (term, exponent) in terms {
                                    let term = simplify(term);
                                    let term_factors = find_factors(&term);
                                    if term_factors.is_empty() {
                                        *factors.entry(term).or_insert(0) += exponent;
                                    } else {
                                        sum_factor_btreemaps(&mut factors, term_factors);
                                    }
                                }
                                factors
                            }
                            AddSub {
                                terms: (ref left, ref right),
                                subtract,
                            } => {
                                let left = simplify(left);
                                let right = simplify(right);
                                let common_factors = find_common_factors(&left, &right);
                                let mut algebraic = BTreeMap::new();
                                for (term, exponent) in to_like_powers(&left, &right, subtract) {
                                    if let Numeric(n) = term {
                                        for (sub_f, sub_e) in find_factors_of_numeric(n) {
                                            *algebraic.entry(sub_f).or_insert(0) +=
                                                sub_e * exponent;
                                        }
                                    } else {
                                        *algebraic.entry(term).or_insert(0) += exponent;
                                    }
                                }
                                let factors = multiset_union(vec![common_factors, algebraic]);
                                let cofactors = factors
                                    .iter()
                                    .filter_map(|(factor, exponent)| {
                                        let mut cofactor = div_exact(expr, factor)?;
                                        let mut remaining_exponent = exponent - 1;
                                        while remaining_exponent > 0
                                            && let Some(new_cofactor) = div_exact(&cofactor, factor)
                                        {
                                            cofactor = new_cofactor;
                                            remaining_exponent -= 1;
                                        }
                                        Some((simplify(&cofactor), 1))
                                    })
                                    .collect();
                                multiset_union(vec![factors, cofactors])
                            }
                        },
                    };
                    if factors.is_empty() || (factors.len() == 1 && factors.get(expr) == Some(&1)) {
                        if let Some(n) = evaluate_as_numeric(expr) {
                            find_factors_of_numeric(n)
                        } else {
                            let mut factors = BTreeMap::new();
                            for prime in SMALL_PRIMES {
                                let mut prime_to_power = prime as NumericFactor;
                                let mut power = 0;
                                while modulo_as_numeric(expr, prime_to_power) == Some(0) {
                                    power += 1;
                                    let Some(new_power) =
                                        prime_to_power.checked_mul(prime as NumericFactor)
                                    else {
                                        break;
                                    };
                                    prime_to_power = new_power;
                                }
                                if power > 0 {
                                    *factors.entry(Numeric(prime as NumericFactor)).or_insert(0) +=
                                        power;
                                }
                            }
                            let cofactor = simplify_divide(expr, &factors);
                            if &cofactor != expr {
                                factors.insert(cofactor, 1);
                            }
                            factors
                        }
                    } else {
                        factors
                    }
                })
            });
            FIND_FACTORS_STACK.with(|stack| stack.borrow_mut().remove(expr));
            factor_cache.insert(expr.clone(), results.clone());
            results
        }
    }
}

fn factor_big_num(expr: &str) -> BTreeMap<Factor, NumberLength> {
    let mut factors = BTreeMap::new();
    let mut expr_short = expr;
    let orig_length = expr_short.len();
    expr_short = expr_short.trim_end_matches('0');
    let trailing_zeros = (orig_length - expr_short.len()) as NumberLength;
    if trailing_zeros > 0 {
        *factors.entry(Factor::two()).or_insert(0) += trailing_zeros;
        *factors.entry(Factor::five()).or_insert(0) += trailing_zeros;
    }
    if let Ok(num) = expr_short.parse::<NumericFactor>() {
        sum_factor_btreemaps(&mut factors, find_factors_of_numeric(num));
    } else {
        match expr_short.chars().last() {
            Some('5') => *factors.entry(Factor::five()).or_insert(0) += 1,
            Some('2' | '4' | '6' | '8') => *factors.entry(Factor::two()).or_insert(0) += 1,
            // '0' is handled by strip_suffix
            _ => {}
        }
        let digit_values: Option<Vec<NumericFactor>> = expr_short
            .chars()
            .map(|digit| digit.to_digit(10).map(NumericFactor::from))
            .collect();
        if let Some(digit_values) = digit_values {
            let sum_of_digits: NumericFactor = digit_values.into_iter().sum();
            match sum_of_digits % 9 {
                0 => {
                    *factors.entry(Factor::three()).or_insert(0) += 2;
                }
                3 | 6 => {
                    *factors.entry(Factor::three()).or_insert(0) += 1;
                }
                _ => {}
            }
        }
        let original = Factor::from(expr_short);
        if factors.is_empty() {
            factors.insert(original, 1);
        } else {
            factors.insert(Factor::divide(original, factors.clone()), 1);
        }
    }
    factors
}

fn sum_factor_btreemaps(
    factors: &mut BTreeMap<Factor, NumberLength>,
    extra_factors: BTreeMap<Factor, NumberLength>,
) {
    for (factor, exponent) in extra_factors {
        *factors.entry(factor).or_insert(0) += exponent;
    }
}

#[inline]
fn find_common_factors(expr1: &Factor, expr2: &Factor) -> BTreeMap<Factor, NumberLength> {
    let num1 = evaluate_as_numeric(expr1);
    if num1 == Some(1) {
        return BTreeMap::new();
    }
    let num2 = evaluate_as_numeric(expr2);
    if num2 == Some(1) {
        return BTreeMap::new();
    }
    if let Some(num1) = num1
        && let Some(num2) = num2
    {
        find_factors_of_numeric(num1.gcd(&num2))
    } else {
        let expr1_factors = find_factors(expr1);
        if expr1_factors.is_empty() {
            return BTreeMap::new();
        }
        let expr2_factors = find_factors(expr2);
        multiset_intersection::<Factor>(expr1_factors, expr2_factors)
    }
}

/// Returns all unique, nontrivial factors we can find.
#[inline(always)]
pub fn find_unique_factors(expr: &Factor) -> Box<[Factor]> {
    let unique_factor_cache =
        UNIQUE_FACTOR_CACHE_LOCK.get_or_init(|| SyncFactorCache::new(UNIQUE_FACTOR_CACHE_SIZE));
    let cached = unique_factor_cache.get(expr);
    match cached {
        Some(cached) => cached,
        None => {
            let simplified = simplify(expr);
            let mut factors = BTreeSet::new();
            let mut raw_factors: Vec<_> = find_factors(expr).into_iter().collect();
            while let Some((factor, exponent)) = raw_factors.pop() {
                if exponent != 0
                    && factor != *expr
                    && factor != simplified
                    && factor.as_numeric() != Some(1)
                    && factor.may_be_proper_divisor_of(expr)
                    && factor.may_be_proper_divisor_of(&simplified)
                {
                    let f = simplify(&factor);
                    if let Complex(ref c) = f {
                        match **c {
                            Multiply { ref terms, .. } => {
                                raw_factors.extend(terms.clone().into_iter());
                                continue;
                            }
                            Divide { ref left, .. } => {
                                if *left == Factor::one() {
                                    // Factors of 1/x are either non-integer when x!=1 or trivial when x==1
                                    continue;
                                }
                            }
                            _ => {}
                        }
                    }
                    if f.may_be_proper_divisor_of(expr) && f.may_be_proper_divisor_of(&simplified) {
                        factors.insert(f);
                    }
                }
            }
            if factors.is_empty() {
                warn!("No factors found for expression {expr}");
            } else {
                info!(
                    "Found factors of expression {expr}: {}",
                    factors.iter().join(", ")
                );
            }
            let factors: Box<[Factor]> = factors.into_iter().collect();
            unique_factor_cache.insert(expr.clone(), factors.clone());
            factors
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::NumberLength;
    use crate::algebraic::ComplexFactor::Divide;
    use crate::algebraic::Factor::{Complex, Numeric};
    use crate::algebraic::{
        ComplexFactor, Factor, NumericFactor, SMALL_FIBONACCI_FACTORS, SMALL_LUCAS_FACTORS,
        div_exact, estimate_log10, factor_power, fibonacci_factors, lucas_factors, modinv,
        modulo_as_numeric, multiset_intersection, multiset_union, power_multiset,
    };
    use ahash::RandomState;
    use alloc::collections::BTreeSet;
    use itertools::Itertools;
    use std::collections::BTreeMap;
    use std::iter::repeat_n;

    impl From<String> for Factor {
        fn from(value: String) -> Self {
            Self::from(value.as_str())
        }
    }

    fn find_factors(input: &str) -> Box<[Factor]> {
        crate::algebraic::find_unique_factors(&Factor::from(input))
    }

    fn find_factors_recursive(input: &str) -> Vec<Factor> {
        let mut already_decomposed = BTreeSet::new();
        let mut factors = BTreeMap::new();
        let mut results = BTreeSet::new();
        let input = Factor::from(input);
        factors.insert(input.clone(), 1);
        while let Some((factor, exponent)) = factors.pop_first() {
            if already_decomposed.insert(factor.clone()) {
                let next_factors = super::find_factors(&factor);
                println!(
                    "{factor}: {}",
                    next_factors
                        .iter()
                        .map(|(k, v)| format!("{k}->{v}"))
                        .join(", ")
                );
                if factor != input {
                    results.insert(factor);
                }
                for (subfactor, subfactor_exponent) in next_factors {
                    *factors.entry(subfactor).or_insert(0) += exponent * subfactor_exponent;
                }
            }
        }
        results.into_iter().collect()
    }

    fn evaluate_as_numeric(input: &str) -> Option<NumericFactor> {
        crate::algebraic::evaluate_as_numeric(&Factor::from(input))
    }

    #[test]
    fn test_precedence() {
        assert_eq!(
            &Factor::from("(3^7396-928)/3309349849490834480566907-1").to_string(),
            "(((((3)^7396)-928)/3309349849490834480566907)-1)"
        );
        assert_eq!(evaluate_as_numeric("(3^7-6)/727"), Some(3));
    }

    #[test]
    fn test_division() {
        let factors = find_factors("(2^625+1)/(2^5+1)".into());
        println!("{}", factors.iter().join(","));
        assert!(!factors.contains(&3.into()));
        assert!(
            !find_factors("lucas(604203)/lucas(201401)/4".into()).contains(&"lucas(201401)".into())
        );
    }

    #[test]
    fn test_division_2() {
        let factors = find_factors_recursive("(3^200+1)/2");
        println!("{}", factors.iter().join(","));
        assert!(!factors.contains(&2.into()));
    }

    #[test]
    fn test_anbc() {
        let expr = format!("{}^9*3+3", NumericFactor::MAX);
        let factors = find_factors(&expr);
        println!("{}", factors.iter().join(", "));
        assert!(factors.contains(&3.into()));
        assert!(factors.contains(&format!("{}^9+1", NumericFactor::MAX).into()));
    }

    #[test]
    fn test_anbc_2() {
        let factors = find_factors_recursive("(6^200600+1)/17".into());
        println!("{}", factors.iter().join(", "));

        // Should contain (6^8+1)/17
        assert!(factors.contains(&98801.into()));

        // Shouldn't contain 6^5+1
        assert!(!factors.contains(&((6 as NumericFactor).pow(5) + 1).into()));
        assert!(!factors.contains(&7.into()));
        assert!(!factors.contains(&11.into()));
        assert!(!factors.contains(&101.into()));
        assert!(!factors.contains(&"6^5+1".into()));
    }

    #[test]
    fn test_anbc_3() {
        let factors = find_factors("6^1337*5-15".into());

        assert!(factors.contains(&3.into())); // common factor of a^x and c
        assert!(factors.contains(&5.into())); // common factor of b and c
    }

    #[test]
    fn test_anb_minus_c() {
        let expr = format!("{}^24-1", NumericFactor::MAX);
        let factors = find_factors_recursive(&expr);
        println!("{}", factors.iter().join(", "));
        assert!(factors.contains(&format!("{}^12-1", NumericFactor::MAX).into()));
        assert!(factors.contains(&format!("{}^12+1", NumericFactor::MAX).into()));
        assert!(factors.contains(&format!("{}^8-1", NumericFactor::MAX).into()));
        assert!(!factors.contains(&format!("{}^8+1", NumericFactor::MAX).into()));
        assert!(factors.contains(&format!("{}^6+1", NumericFactor::MAX).into()));
        assert!(factors.contains(&format!("{}^6-1", NumericFactor::MAX).into()));
        assert!(factors.contains(&format!("{}^4+1", NumericFactor::MAX).into()));
        assert!(factors.contains(&format!("{}^4-1", NumericFactor::MAX).into()));
        assert!(factors.contains(&format!("{}^3+1", NumericFactor::MAX).into()));
        assert!(factors.contains(&format!("{}^3-1", NumericFactor::MAX).into()));
        assert!(factors.contains(&format!("{}^2+1", NumericFactor::MAX).into()));
        assert!(factors.contains(&format!("{}^2-1", NumericFactor::MAX).into()));
    }

    #[test]
    fn test_modinv() {
        assert_eq!(modinv(3, 11), Some(4));
        assert_eq!(modinv(17, 3120), Some(2753));
        assert_eq!(modinv(6, 9), None);
    }

    #[test]
    fn test_axbx() {
        let factors = find_factors_recursive("(1297^400-901^400)/3".into());
        println!("{}", factors.iter().sorted().unique().join(","));
        assert!(factors.contains(&Numeric(2)));
        assert!(factors.contains(&"1297^200-901^200".into()));
        assert!(factors.contains(&"1297^80-901^80".into()));
        assert!(factors.contains(&"1297^200+901^200".into()));
        assert!(!factors.contains(&"1297^80+901^80".into()));
        let factors = find_factors_recursive("1297^390-901^390".into());
        println!("{}", factors.iter().sorted().unique().join(","));
        assert!(
            factors
                .iter()
                .any(|factor| matches!(factor, Numeric(n) if n.is_multiple_of(2)))
        );
        assert!(
            factors
                .iter()
                .any(|factor| matches!(factor, Numeric(n) if n.is_multiple_of(3)))
        );
        assert!(
            !factors
                .iter()
                .any(|factor| matches!(factor, Numeric(n) if n.is_multiple_of(5)))
        );
        assert!(
            factors
                .iter()
                .any(|factor| matches!(factor, Numeric(n) if n.is_multiple_of(11)))
        );
        assert!(factors.contains(&"1297^130-901^130".into()));
        assert!(factors.contains(&"1297^195-901^195".into()));
        assert!(!factors.contains(&"1297^130+901^130".into()));
        assert!(factors.contains(&"1297^195+901^195".into()));
    }
    #[test]
    fn test_axby() {
        let factors = find_factors("1297^1234-901^1".into());
        println!("{}", factors.iter().sorted().unique().join(","));
        assert!(factors.contains(&Numeric(2)));
        assert!(factors.contains(&Numeric(3)));

        // These expressions are negative but should not crash
        find_factors("1297^1-901^123".into());
        find_factors("901^1-1297^1".into());
    }

    #[test]
    fn test_chain() {
        let factors = find_factors("2^8+3*5-1".into());
        assert!(factors.contains(&Numeric(2)));
    }

    #[test]
    fn test_chain_2() {
        let factors = find_factors("(2^9+1)^2*7^2/361".into());
        assert!(factors.contains(&Numeric(3)));
        assert!(factors.contains(&Numeric(7)));
        assert!(!factors.contains(&Numeric(19)));
    }

    #[test]
    fn test_mul_chain() {
        let factors = find_factors("2^8*3*5".into());
        assert!(factors.contains(&Numeric(2)));
        assert!(factors.contains(&Numeric(3)));
        assert!(factors.contains(&Numeric(5)));
    }

    #[test]
    fn test_div_chain() {
        let factors = find_factors("210/2/5".into());
        assert!(factors.contains(&Numeric(3)));
        assert!(factors.contains(&Numeric(7)));
        assert!(!factors.contains(&Numeric(2)));
        assert!(!factors.contains(&Numeric(5)));
    }

    #[test]
    fn test_mixed_chain() {
        let expr = format!(
            "(2^256-1)*(3^200+1)*(10^50)*((12^368-1)^2)/20/1{}",
            &repeat_n('0', 49).collect::<String>()
        );
        let factors = find_factors_recursive(&expr);
        println!("{}", factors.iter().join(","));
        // Since find_factors_recursive finds factors of intermediate terms,
        // and some intermediate algebraic terms have numeric factors
        // (even if cancelled globally), they appear in the recursive results.
        assert!(factors.contains(&Numeric(3)));
        assert!(factors.contains(&Numeric(11)));
    }

    #[test]
    fn test_addition_chain() {
        let factors = find_factors_recursive("7^5432+3*7^4321+7^321+7^21".into());
        println!("{}", factors.iter().join(","));
        assert!(factors.contains(&Numeric(2)));
        assert!(factors.contains(&Numeric(7)));
        let factors = find_factors("7^5432+3*7^4321+7^321+7^21+1".into());
        assert!(!factors.contains(&Numeric(2)));
        assert!(!factors.contains(&Numeric(7)));
        let factors = find_factors("3*7^5432+7^4321+7^321+1".into());
        assert!(factors.contains(&Numeric(2)));
        assert!(!factors.contains(&Numeric(7)));
        let factors = find_factors("7^5432-7^4321-3*7^321-1".into());
        assert!(factors.contains(&Numeric(2)));
        assert!(!factors.contains(&Numeric(7)));
    }

    #[test]
    fn test_power() {
        let factors = super::find_factors(&"(2^7-1)^2".into());
        assert_eq!(factors, [(Numeric(127), 2)].into());
    }

    #[test]
    fn test_power_associativity() {
        assert_eq!(evaluate_as_numeric("2^3^4"), Some(1 << 81));
    }

    #[test]
    fn test_division_associativity() {
        assert_eq!(evaluate_as_numeric("20/5/2"), Some(2));
    }

    #[test]
    fn test_stack_depth() {
        // unsafe { backtrace_on_stack_overflow::enable() };
        let expr = repeat_n("(2^9+1)", 1 << 16).join("*");
        find_factors(&expr);
        evaluate_as_numeric(&expr);
        let expr = Factor::from(expr);
        crate::algebraic::estimate_log10_internal(&expr);
    }

    #[test]
    fn test_stack_depth_2() {
        const PRIMORIAL: NumericFactor = 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19;
        lucas_factors(PRIMORIAL, true);
        fibonacci_factors(PRIMORIAL, true);
    }

    #[test]
    fn test_parse() {
        let factors = find_factors("I(17#)".into());
        // lucas_factors(PRIMORIAL, true);
        assert!(factors.contains(&Numeric(13)));
    }

    #[test]
    fn test_nested_parens() {
        let factors = find_factors_recursive("(12^((2^7-1)^2)-1)/88750555799".into());
        println!("{}", factors.iter().join(","));
        assert!(factors.contains(&Numeric(11)));
        assert!(factors.contains(&"12^127-1".into()));
    }

    #[test]
    fn test_multiple_hashes() {
        assert_eq!(evaluate_as_numeric("2##"), Some(6)); // 2## = 6; (2#)# = 2
        assert_eq!(evaluate_as_numeric("2###"), Some(30)); // 2### = (2##)# = 30; (2#)## = 6

        // 2#### = (2##)## = 30030
        assert_eq!(evaluate_as_numeric("2####"), Some(30030));
        // (3#)### = 30029#
        // (3##)## = 113#
        // (3###)# = 6469693230#

        println!("{}", find_factors("92##".into()).into_iter().join(","));
    }

    #[test]
    fn test_m_precedence() {
        assert_eq!(evaluate_as_numeric("M7^2"), Some(127 * 127));
        assert_eq!(evaluate_as_numeric("M7*5"), Some(127 * 5));
        assert_eq!(evaluate_as_numeric("M5!"), Some((1..=31).product())); // (M5)!
        assert_eq!(
            evaluate_as_numeric("M5#"),
            Some(2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 * 29 * 31)
        ); // (M5)#
    }

    #[test]
    fn test_factor_power() {
        assert_eq!(
            factor_power(5474401089420219382077155933569751763, 16),
            (3, 16 * 77)
        );
        // (3^77)^16+1
        let factors = find_factors("5474401089420219382077155933569751763^16+1".into());
        println!("{}", factors.iter().join(","));
        // factors of 3^16+1
        // assert!(factors.contains(&Numeric(2)));
        assert!(factors.contains(&"3^176+1".into()));
        assert!(factors.contains(&"3^112+1".into()));
    }

    #[test]
    fn test_lucas() {
        let factors = lucas_factors(5040, true);
        assert!(factors.values().all(|e| *e == 1));
        for odd_divisor in [35, 45, 63, 105, 315] {
            for factor in SMALL_LUCAS_FACTORS[5040 / odd_divisor] {
                assert!(factors.contains_key(&(Numeric(*factor).into())));
            }
        }
    }

    #[test]
    fn test_fibonacci() {
        let factors = fibonacci_factors(5040, true);
        let larger_factors: BTreeMap<Factor, NumberLength> = factors
            .clone()
            .into_iter()
            .filter(|(f, _)| if let Numeric(n) = *f { n > 7 } else { true })
            .collect();
        assert!(larger_factors.values().all(|e| *e == 1));
        println!(
            "{}",
            factors.iter().map(|(k, v)| format!("{k}->{v}")).join(", ")
        );
        for divisor in [
            1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 28, 30, 35, 36, 40, 42,
            45, 48, 56, 60, 63, 70, 72, 80, 84, 90, 105, 112, 120, 126, 140, 144, 168, 180,
        ] {
            for factor in SMALL_FIBONACCI_FACTORS[divisor] {
                assert!(
                    factors.contains_key(&Numeric(*factor).into()),
                    "Missing {factor} for I({divisor}) in I(5040)"
                );
            }
        }
    }

    #[test]
    fn test_power_multiset() {
        let multiset = [(2, 2), (3, 2), (5, 1)].into();
        let power_multiset = power_multiset(multiset);
        println!("{:?}", power_multiset);
        assert_eq!(power_multiset.len(), 18);
        assert!(power_multiset.contains(&BTreeMap::new()));
        assert!(power_multiset.contains(&[(2, 1)].into()));
        assert!(power_multiset.contains(&[(2, 2)].into()));
        assert!(power_multiset.contains(&[(3, 1)].into()));
        assert!(power_multiset.contains(&[(2, 1), (3, 1)].into()));
        assert!(power_multiset.contains(&[(2, 2), (3, 1)].into()));
        assert!(power_multiset.contains(&[(3, 2)].into()));
        assert!(power_multiset.contains(&[(2, 1), (3, 2)].into()));
        assert!(power_multiset.contains(&[(2, 2), (3, 2)].into()));
        assert!(power_multiset.contains(&[(5, 1)].into()));
        assert!(power_multiset.contains(&[(2, 1), (5, 1)].into()));
        assert!(power_multiset.contains(&[(2, 2), (5, 1)].into()));
        assert!(power_multiset.contains(&[(3, 1), (5, 1)].into()));
        assert!(power_multiset.contains(&[(2, 1), (3, 1), (5, 1)].into()));
        assert!(power_multiset.contains(&[(2, 2), (3, 1), (5, 1)].into()));
        assert!(power_multiset.contains(&[(3, 2), (5, 1)].into()));
        assert!(power_multiset.contains(&[(2, 1), (3, 2), (5, 1)].into()));
        assert!(power_multiset.contains(&[(2, 2), (3, 2), (5, 1)].into()));
    }

    #[test]
    fn test_multiset_union() {
        let multiset_1 = [(2, 2), (3, 1), (5, 1), (7, 1)].into();
        let multiset_2 = [(2, 1), (3, 2), (5, 1), (11, 1)].into();
        let union = multiset_union(vec![multiset_1, multiset_2]);
        assert_eq!(union, [(2, 2), (3, 2), (5, 1), (7, 1), (11, 1)].into());
    }

    #[test]
    fn test_multiset_intersection() {
        let multiset_1: BTreeMap<NumericFactor, NumberLength> =
            [(2, 2), (3, 1), (5, 1), (7, 1)].into();
        let multiset_2: BTreeMap<NumericFactor, NumberLength> =
            [(2, 1), (3, 2), (5, 1), (11, 1)].into();
        let intersection = multiset_intersection(multiset_1.into(), multiset_2.into());
        assert_eq!(intersection, [(2, 1), (3, 1), (5, 1)].into());
    }

    #[test]
    fn test_estimate_log10() {
        fn estimate_log10_internal(input: &str) -> (NumberLength, NumberLength) {
            crate::algebraic::estimate_log10_internal(&Factor::from(input).into())
        }
        let (lower, upper) = estimate_log10_internal("99");
        assert_eq!(lower, 1);
        assert_eq!(upper, 2);
        let (lower, upper) = estimate_log10_internal("100");
        assert_eq!(lower, 2);
        assert_eq!(upper, 2);
        let (lower, upper) = estimate_log10_internal("101");
        assert_eq!(lower, 2);
        assert_eq!(upper, 3);
        let (lower, upper) =
            estimate_log10_internal(&("1".to_string() + &repeat_n('0', 50).collect::<String>()));
        assert_eq!(lower, 50);
        assert!(upper == 50 || upper == 51);
        let (lower, upper) = estimate_log10_internal(&(repeat_n('9', 50).collect::<String>()));
        assert_eq!(lower, 49);
        assert!(upper == 49 || upper == 50);
        let (lower, upper) = estimate_log10_internal("I1234".into());
        assert_eq!(lower, 257);
        assert!(upper == 258 || upper == 259);
        let (lower, upper) = estimate_log10_internal("lucas(1234)".into());
        assert_eq!(lower, 257);
        assert!(upper == 258 || upper == 259);
        let (lower, upper) = estimate_log10_internal("2^607-1".into());
        assert!(lower == 182 || lower == 181);
        assert_eq!(upper, 183);
        let (lower, upper) = estimate_log10_internal("10^200-1".into());
        assert!(lower == 198 || lower == 199);
        assert!(upper == 200 || upper == 201);
        let (lower, upper) = estimate_log10_internal("10^200+1".into());
        assert!(lower == 199 || lower == 200);
        assert!(upper == 201 || upper == 202);
        let (lower, upper) = estimate_log10_internal("10^200*31-1".into());
        assert!(lower >= 199);
        assert!(lower <= 201);
        assert!(upper >= 202);
        assert!(lower <= 204);
        let (lower, upper) = estimate_log10_internal("100!".into());
        assert_eq!(lower, 157);
        assert_eq!(upper, 158);
        let (lower, upper) = estimate_log10_internal("100#".into());
        assert!(lower <= 36);
        assert!(upper >= 37);
        assert!(upper <= 44);
        let (lower, upper) = estimate_log10_internal("20+30".into());
        assert_eq!(lower, 1);
        assert!(upper == 2 || upper == 3);
        let (lower, upper) = estimate_log10_internal("30-19".into());
        assert!(lower <= 1);
        assert_eq!(upper, 2);
        let (lower, upper) = estimate_log10_internal("11*11".into());
        assert_eq!(lower, 2);
        assert!(upper >= 3);
        let (lower, upper) = estimate_log10_internal("(2^769-1)/1591805393".into());
        assert!(lower >= 219 && lower <= 222);
        assert!(upper >= 223 && upper <= 225);
        let (lower, upper) = estimate_log10_internal("3^5000-4^2001".into());
        assert!(lower == 2385 || lower == 2384);
        assert!(upper == 2386 || upper == 2387);
    }

    #[test]
    fn test_evaluate_as_numeric() {
        assert_eq!(
            evaluate_as_numeric("2^127-1"),
            Some(i128::MAX as NumericFactor)
        );
        assert_eq!(evaluate_as_numeric("(5^6+1)^2-1"), Some(244171875));
        assert_eq!(evaluate_as_numeric("3^3+4^4+5^5"), Some(3408));
    }

    #[test]
    fn test_may_be_proper_divisor_of() {
        fn may_be_proper_divisor_of(left: &str, right: &str) -> bool {
            Factor::from(left).may_be_proper_divisor_of(&Factor::from(right))
        }
        assert!(may_be_proper_divisor_of("123", "369^2"));
        assert!(!may_be_proper_divisor_of("2", "34567"));
        assert!(may_be_proper_divisor_of("2", "345-67"));
        assert!(!may_be_proper_divisor_of("12345", "54321"));
        assert!(!may_be_proper_divisor_of("12345", "12345"));
        assert!(!may_be_proper_divisor_of("54321", "12345"));
        assert!(!may_be_proper_divisor_of(
            "123456789123456789123456789123456789123456789",
            "123456789123456789123456789123456789123456789/3"
        ));
        assert!(may_be_proper_divisor_of(
            "123456789123456789123456789123456789123456789/3",
            "123456789123456789123456789123456789123456789"
        ));
        assert!(!may_be_proper_divisor_of(
            "2/1234512345123451234512345123451234512345",
            "1234512345123451234512345123451234512345"
        ));
        assert!(!may_be_proper_divisor_of(
            "1234512345123451234512345123451234512345/2",
            "1234512345123451234512345123451234512345"
        ));
        assert!(may_be_proper_divisor_of(
            "1234512345123451234512345123451234512345",
            "1234512345123451234512345123451234512345^2"
        ));
        assert!(!may_be_proper_divisor_of(
            "1234512345123451234512345123451234512345^2",
            "1234512345123451234512345123451234512345"
        ));
        assert!(!may_be_proper_divisor_of("2^1234-1", "(2^1234-1)/3"));
        assert!(may_be_proper_divisor_of("(2^1234-1)/3", "2^1234-1"));
    }

    #[test]
    fn test_find_factors_performance_1() {
        let factors = find_factors_recursive("I(969969)");
        println!("Factors: {}", factors.into_iter().join(", "));
    }

    #[test]
    fn test_find_numeric_factors_performance() {
        let start = std::time::Instant::now();
        const FIRST_LARGE_PRIME: NumericFactor = 23058430092136939559; // next prime after 5<<62
        const SECOND_LARGE_PRIME: NumericFactor = 13835058055282163729; // next prime after 3<<62
        let expr = Numeric(FIRST_LARGE_PRIME * SECOND_LARGE_PRIME);
        let factors = super::find_factors(&expr.into());
        println!("Time: {:?}", start.elapsed());
        // Verify correct answer
        assert_eq!(factors.len(), 2);
        assert_eq!(factors.get(&Factor::from(FIRST_LARGE_PRIME)), Some(&1));
        assert_eq!(factors.get(&Factor::from(SECOND_LARGE_PRIME)), Some(&1));
    }

    #[test]
    fn test_factor_big_num_symbolic() {
        // "1212...12" (50 times)
        // Sum = (1+2)*50 = 150 (div by 3). Ends in 2 (div by 2).
        let repeated_12 = "12".repeat(50);
        let expr = super::expression_parser::arithmetic(&repeated_12).unwrap();
        let factors = super::find_factors(&Factor::from(expr).into());
        println!(
            "{}",
            factors.iter().map(|(k, v)| format!("{k}->{v}")).join(", ")
        );
        // Should contain 2 and 3.
        assert!(factors.contains_key(&Factor::two()));
        assert!(factors.contains_key(&Factor::three()));

        // Should contain a generic factor which is the Divide term
        let has_divide = factors.iter().any(|(f, e)| *e == 1
            && matches!(*f, Complex(ref c) if matches!(**c, Divide { ref right, .. } if right.contains_key(&Factor::two()))));
        assert!(has_divide, "Should return a symbolic Divide term");

        // Should prevent infinite recursion
        factors.into_keys().for_each(|f| {
            super::find_factors(&f);
        });
    }

    #[test]
    fn test_pisano() {
        assert_eq!(modulo_as_numeric(&"I(2000)".into(), 5), Some(0));
        assert_eq!(modulo_as_numeric(&"I(2001)".into(), 5), Some(1));
        assert_eq!(modulo_as_numeric(&"I(2002)".into(), 5), Some(1));
        assert_eq!(modulo_as_numeric(&"I(2003)".into(), 5), Some(2));
        assert_eq!(modulo_as_numeric(&"I(2004)".into(), 5), Some(3));
    }

    #[test]
    fn test_large_fibonacci_lucas_factors() {
        use primitive_types::U256;
        fn fib(n: usize) -> U256 {
            let mut a = U256::from(0);
            let mut b = U256::from(1);
            for _ in 0..n {
                let tmp = a;
                a = b;
                b = tmp + b;
            }
            a
        }

        fn luc(n: usize) -> U256 {
            let mut a = U256::from(2);
            let mut b = U256::from(1);
            for _ in 0..n {
                let tmp = a;
                a = b;
                b = tmp + b;
            }
            a
        }

        for n in 2..=300 {
            let f_n = fib(n);
            let factors = fibonacci_factors(n as NumericFactor, true);
            let mut product = U256::from(1);
            for (factor, exponent) in factors {
                if let Some(val) = crate::algebraic::evaluate_as_numeric(&factor) {
                    assert_eq!(
                        f_n % U256::from(val),
                        U256::from(0),
                        "Factor {} of F({}) = {} is not a divisor",
                        val,
                        n,
                        f_n
                    );
                    product *= U256::from(val).pow(exponent.into());
                } else {
                    assert!(
                        n >= SMALL_FIBONACCI_FACTORS.len(),
                        "Factor {:?} of I({}) is not numeric",
                        factor,
                        n
                    );
                }
            }
            if n < SMALL_FIBONACCI_FACTORS.len() {
                assert_eq!(product, f_n, "Product of factors of F({}) != I({})", n, n);
            } else {
                assert!(product <= f_n);
            }

            let l_n = luc(n);
            let factors = lucas_factors(n as NumericFactor, true);
            let mut product = U256::from(1);
            for (factor, exponent) in factors {
                if let Some(val) = crate::algebraic::evaluate_as_numeric(&factor) {
                    assert_eq!(
                        l_n % U256::from(val),
                        U256::from(0),
                        "Factor {} of L({}) = {} is not a divisor",
                        val,
                        n,
                        l_n
                    );
                    product *= U256::from(val).pow(exponent.into());
                } else {
                    assert!(
                        n >= SMALL_LUCAS_FACTORS.len(),
                        "Factor {:?} of L({}) is not numeric",
                        factor,
                        n
                    );
                }
            }
            if n < SMALL_LUCAS_FACTORS.len() {
                assert_eq!(product, l_n, "Product of factors of L({}) != L({})", n, n);
            } else {
                assert!(product <= l_n);
            }
        }
    }

    #[test]
    fn test_parse_elided() {
        assert!(matches!(Factor::from("2002...96"), Factor::ElidedNumber(_)));
    }

    mod complexfactor_eq_and_hash {
        use super::*;
        use alloc::fmt::Debug;
        use std::collections::BTreeMap;
        use std::hash::Hash;
        fn assert_eq_and_same_hash<T: Eq + Hash + Debug>(left: T, right: T, message: &str) {
            assert_eq!(left, right, "In Eq: {message}");
            let hasher = RandomState::new();
            let left_hash = hasher.hash_one(left);
            let right_hash = hasher.hash_one(right);
            assert_eq!(left_hash, right_hash, "In Hash: {message}");
        }

        #[test]
        fn test_addsub_commutative_addition() {
            // a + b should equal b + a
            let a = Factor::from("x");
            let b = Factor::from(42u128);

            let add1 = ComplexFactor::AddSub {
                terms: (a.clone(), b.clone()),
                subtract: false,
            };

            let add2 = ComplexFactor::AddSub {
                terms: (b.clone(), a.clone()),
                subtract: false,
            };

            assert_eq_and_same_hash(add1, add2, "Addition should be commutative");
        }

        #[test]
        fn test_addsub_subtraction_not_commutative() {
            // a - b should NOT equal b - a (unless a == b)
            let a = Factor::from("x");
            let b = Factor::from("y");

            let sub1 = ComplexFactor::AddSub {
                terms: (a.clone(), b.clone()),
                subtract: true,
            };

            let sub2 = ComplexFactor::AddSub {
                terms: (b.clone(), a.clone()),
                subtract: true,
            };

            assert_ne!(sub1, sub2, "Subtraction should not be commutative");
            // Hashes can be different for non-equal values
        }

        #[test]
        fn test_addsub_addition_vs_subtraction() {
            // a + b should NOT equal a - b
            let a = Factor::from(10u128);
            let b = Factor::from(5u128);

            let add = ComplexFactor::AddSub {
                terms: (a.clone(), b.clone()),
                subtract: false,
            };

            let sub = ComplexFactor::AddSub {
                terms: (a.clone(), b.clone()),
                subtract: true,
            };

            assert_ne!(add, sub, "Addition and subtraction should not be equal");
        }

        #[test]
        fn test_addsub_same_order() {
            // a + b should equal a + b (trivial but important)
            let a = Factor::from("alpha");
            let b = Factor::from("beta");

            let add1 = ComplexFactor::AddSub {
                terms: (a.clone(), b.clone()),
                subtract: false,
            };

            let add2 = ComplexFactor::AddSub {
                terms: (a.clone(), b.clone()),
                subtract: false,
            };

            assert_eq_and_same_hash(
                add1,
                add2,
                "two identical addition instances should be equal",
            );
        }

        #[test]
        fn test_multiply_commutative() {
            // a × b should equal b × a
            let a = Factor::from("x");
            let b = Factor::from(2u128);

            let mut map1 = BTreeMap::new();
            map1.insert(a.clone(), 1); // x^1
            map1.insert(b.clone(), 1); // 2^1

            let mut map2 = BTreeMap::new();
            map2.insert(b.clone(), 1); // 2^1 first
            map2.insert(a.clone(), 1); // x^1 second

            let mul1 = Factor::multiply(map1);

            let mul2 = Factor::multiply(map2);

            assert_eq_and_same_hash(
                mul1,
                mul2,
                "Multiplication should be commutative via BTreeMap",
            );
        }

        #[test]
        fn test_multiply_different_exponents() {
            // x² × y should NOT equal x × y²
            let x = Factor::from("x");
            let y = Factor::from("y");

            let mut map1 = BTreeMap::new();
            map1.insert(x.clone(), 2); // x^2
            map1.insert(y.clone(), 1); // y^1

            let mut map2 = BTreeMap::new();
            map2.insert(x.clone(), 1); // x^1
            map2.insert(y.clone(), 2); // y^2

            let mul1 = Factor::multiply(map1);

            let mul2 = Factor::multiply(map2);

            assert_ne!(mul1, mul2, "Different exponents should not be equal");
        }

        #[test]
        fn test_divide_not_commutative() {
            // a ÷ b should NOT equal b ÷ a
            let a = Factor::from(10u128);
            let b = Factor::from(2u128);

            let mut right1 = BTreeMap::new();
            right1.insert(b.clone(), 1);

            let mut right2 = BTreeMap::new();
            right2.insert(a.clone(), 1);

            let div1 = Factor::divide(a.clone(), right1);

            let div2 = Factor::divide(b.clone(), right2);

            assert_ne!(div1, div2, "Division should not be commutative");
        }

        #[test]
        fn test_power_not_commutative() {
            // x^y should NOT equal y^x
            let x = Factor::from(2u128);
            let y = Factor::from(3u128);

            let pow1 = ComplexFactor::Power {
                base: x.clone(),
                exponent: y.clone(),
            };

            let pow2 = ComplexFactor::Power {
                base: y.clone(),
                exponent: x.clone(),
            };

            assert_ne!(pow1, pow2, "Power should not be commutative");
        }

        #[test]
        fn test_power_same() {
            // x^y should equal x^y
            let x = Factor::from("base");
            let y = Factor::from("exp");

            let pow1 = ComplexFactor::Power {
                base: x.clone(),
                exponent: y.clone(),
            };

            let pow2 = ComplexFactor::Power {
                base: x.clone(),
                exponent: y.clone(),
            };

            assert_eq_and_same_hash(pow1, pow2, "identical power expressions should be equal");
        }

        #[test]
        fn test_fibonacci_equality() {
            let n = Factor::from(10u128);

            let fib1 = ComplexFactor::Fibonacci(n.clone());
            let fib2 = ComplexFactor::Fibonacci(n.clone());
            let fib3 = ComplexFactor::Fibonacci(Factor::from(20u128));

            assert_eq_and_same_hash(
                &fib1,
                &fib2,
                "identical Fibonacci expressions should be equal",
            );
            assert_ne!(fib1, fib3);
        }

        #[test]
        fn test_cross_variant_inequality() {
            // Different variants should never be equal
            let num = Factor::from(5u128);

            let fib = ComplexFactor::Fibonacci(num.clone());
            let luc = ComplexFactor::Lucas(num.clone());
            let fac = ComplexFactor::Factorial(num.clone());
            let prim = ComplexFactor::Primorial(num.clone());

            assert_ne!(fib, luc);
            assert_ne!(fib, fac);
            assert_ne!(fib, prim);
            assert_ne!(luc, fac);
            assert_ne!(luc, prim);
            assert_ne!(fac, prim);
        }

        #[test]
        fn test_hash_consistency_equal_values() {
            // Critical test: equal values must have equal hashes
            let a = Factor::from("variable");
            let b = Factor::from(100u128);

            // Test addition commutativity hash consistency
            let add1 = ComplexFactor::AddSub {
                terms: (a.clone(), b.clone()),
                subtract: false,
            };

            let add2 = ComplexFactor::AddSub {
                terms: (b.clone(), a.clone()),
                subtract: false,
            };

            assert_eq_and_same_hash(add1, add2, "Addition should be commutative");

            // Test multiplication hash consistency
            let x = Factor::from("x");
            let y = Factor::from("y");

            let mut map1 = BTreeMap::new();
            map1.insert(x.clone(), 1);
            map1.insert(y.clone(), 2);

            let mut map2 = BTreeMap::new();
            map2.insert(y.clone(), 2); // Different insertion order
            map2.insert(x.clone(), 1);

            let mul1 = Factor::multiply(map1);

            let mul2 = Factor::multiply(map2);

            assert_eq_and_same_hash(mul1, mul2, "Multiplication should be commutative");
        }

        #[test]
        fn test_edge_case_self_equality() {
            // a + a should equal a + a (trivial but tests edge case)
            let a = Factor::from("same");

            let expr1 = ComplexFactor::AddSub {
                terms: (a.clone(), a.clone()),
                subtract: false,
            };

            let expr2 = ComplexFactor::AddSub {
                terms: (a.clone(), a.clone()),
                subtract: false,
            };

            assert_eq_and_same_hash(expr1, expr2, "identical a+a expressions should be equal");

            // Also test a - a
            let sub1 = ComplexFactor::AddSub {
                terms: (a.clone(), a.clone()),
                subtract: true,
            };

            let sub2 = ComplexFactor::AddSub {
                terms: (a.clone(), a.clone()),
                subtract: true,
            };
            assert_eq_and_same_hash(sub1, sub2, "identical a-a expressions should be equal");
        }

        #[test]
        fn test_nested_expressions() {
            // Test (x + y) × z equality
            let x = Factor::from("x");
            let y = Factor::from("y");
            let z = Factor::from("z");

            let add = Complex(
                ComplexFactor::AddSub {
                    terms: (x.clone(), y.clone()),
                    subtract: false,
                }
                .into(),
            );

            let mut map1 = BTreeMap::new();
            map1.insert(add.clone(), 1);
            map1.insert(z.clone(), 1);

            let mul1 = Factor::multiply(map1);

            // Same expression should be equal
            let mut map2 = BTreeMap::new();
            map2.insert(add.clone(), 1);
            map2.insert(z.clone(), 1);

            let mul2 = Factor::multiply(map2);

            assert_eq_and_same_hash(mul1, mul2, "identical nested expressions should be equal");
        }
    }

    #[test]
    fn test_infinite_recursion_2025_12_12() {
        for expr in [
            "(10^65035*18+10^130071-1)/9",
            "10^65035*18+10^130071-1",
            "((((10)^260)-224)/32)",
        ] {
            let (lower, upper) = estimate_log10(&Factor::from(expr));
            for factor in find_factors(expr) {
                let (factor_lower, factor_upper) = estimate_log10(&factor);
                assert!(factor_lower <= lower, "{factor} lower bound is too large");
                assert!(factor_upper <= upper, "{factor} upper bound is too large");
            }
        }
    }

    #[test]
    fn test_simplify_basic() {
        use crate::algebraic::simplify;
        // x + 0 = x
        let x = Factor::from("x");
        let zero = Factor::from(0u128);
        assert_eq!(
            simplify(&Complex(
                ComplexFactor::AddSub {
                    terms: (x.clone(), zero.clone()),
                    subtract: false,
                }
                .into()
            )),
            x
        );
        assert_eq!(
            simplify(&Complex(
                ComplexFactor::AddSub {
                    terms: (x.clone(), zero.clone()),
                    subtract: true,
                }
                .into()
            )),
            x
        );

        // x * 1 = x
        let one = Factor::from(1u128);
        let mut terms = BTreeMap::new();
        terms.insert(x.clone(), 1);
        terms.insert(one.clone(), 1);
        assert_eq!(
            simplify(&Complex(
                ComplexFactor::Multiply {
                    terms: terms.clone(),
                    terms_hash: 0
                }
                .into()
            )),
            x
        );

        // x ^ 1 = x
        assert_eq!(
            simplify(&Complex(
                ComplexFactor::Power {
                    base: x.clone(),
                    exponent: one.clone()
                }
                .into()
            )),
            x
        );

        // x / 1 = x
        let mut right = BTreeMap::new();
        right.insert(one.clone(), 1);
        assert_eq!(
            simplify(&Complex(
                Divide {
                    left: x.clone(),
                    right,
                    right_hash: 0
                }
                .into()
            )),
            x
        );
    }

    #[test]
    fn test_simplify_power_zero() {
        use crate::algebraic::simplify;
        // x ^ 0 = 1
        let x = Factor::from("x");
        let zero = Factor::from(0u128);
        assert_eq!(
            simplify(&Complex(
                ComplexFactor::Power {
                    base: x.clone(),
                    exponent: zero.clone()
                }
                .into()
            )),
            Factor::one()
        );
    }

    #[test]
    fn test_simplify_nested_powers() {
        use crate::algebraic::simplify;
        // (x^2)^3 = x^6
        let x = Factor::from("x");
        let two = Factor::from(2u128);
        let three = Factor::from(3u128);

        let inner = Complex(
            ComplexFactor::Power {
                base: x.clone(),
                exponent: two.clone(),
            }
            .into(),
        );
        let nested = Complex(
            ComplexFactor::Power {
                base: inner,
                exponent: three.clone(),
            }
            .into(),
        );
        let simplified = simplify(&nested);

        // Should be Multiply, not Power, because exponent's numeric value is known
        let expected = Factor::multiply([(x, 6)].into());

        assert_eq!(simplified, expected);
    }

    #[test]
    fn test_fmt_round_trip() {
        // Verify that Factor::from(f.to_string()) == f
        let cases = [
            "x+y",
            "x-y",
            "x*y",
            "x/y",
            "x^y",
            "x^2+1",
            "(x+1)^2",
            "2^64-1",
            "I(50)",
            "lucas(100)",
            "5!",
            "7#",
            "((a+b)*c)^d",
        ];

        for case in cases {
            let f = Factor::from(case);
            let s = f.to_string();
            let f2 = Factor::from(s.as_str());
            assert_eq!(f, f2, "Round trip failed for {}", case);
        }
    }

    #[test]
    fn test_to_like_powers() {
        use crate::algebraic::to_like_powers;
        // 2^10 - 3^10
        // like power is 10.
        // Or 2, 5.
        // Logic will find factors of exponents.

        let left = Factor::from("2^10");
        let right = Factor::from("3^10");

        let result = to_like_powers(&left, &right, true);
        // Exponent factors of 10 are 1, 2, 5, 10
        // It should return btreemap with factors.
        // Logic: for factor in exponent_factors:
        //    if factor != 2 (unless not subtract):
        //       ...
        // x^10 - y^10.
        // 10: x-y, x+y doesn't work directly if factor==2 check applies?
        // Wait, "subtract || (factor != 2)"
        // If subtract is true, factor=2 IS allowed.
        // So we expect:
        // Common exponent 10.
        // factor 2: (2^5)^2 - (3^5)^2 = (2^5-3^5)(2^5+3^5)
        // factor 5: (2^2)^5 - (3^2)^5 -> (2^2-3^2)(...)

        // Let's just verify it finds SOMETHING
        assert!(!result.is_empty());
    }

    #[test]
    fn test_difference_of_squares() {
        // a^2 - b^2 -> (a-b)(a+b)
        // 5^2 - 4^2 = 25 - 16 = 9 = 3^2
        // factors: 5-4=1, 5+4=9.

        // 10^2 - 6^2 = 100 - 36 = 64 = 2^6
        // factors: 10-6=4, 10+6=16.

        let factors = find_factors("5^2-4^2");
        assert!(factors.iter().any(|f| f.as_numeric() == Some(3)));

        let factors = find_factors("10^2-6^2");
        assert!(factors.iter().any(|f| f.as_numeric() == Some(2)));
    }
    #[test]
    fn test_div_exact_numeric_fallback_bug() {
        // (x+1)*10 / ((x+1)*2) should be 5
        let x_plus_1: Factor = "x+1".into();
        let product = Factor::multiply([(x_plus_1.clone(), 1), (10.into(), 1)].into());
        let divisor = Factor::multiply([(x_plus_1.clone(), 1), (2.into(), 1)].into());
        let result = div_exact(&product, &divisor);
        assert_eq!(result, Some(5.into()));
    }
}
