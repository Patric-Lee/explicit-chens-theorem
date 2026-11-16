import PlattAssemblyKernel
import PlattCertificates.Count131072.C027008
import PlattCertificates.Count131072.C027009
import PlattCertificates.Count131072.C027010
import PlattCertificates.Count131072.C027011
import PlattCertificates.Count131072.C027012
import PlattCertificates.Count131072.C027013
import PlattCertificates.Count131072.C027014
import PlattCertificates.Count131072.C027015
import PlattCertificates.Count131072.C027016
import PlattCertificates.Count131072.C027017
import PlattCertificates.Count131072.C027018
import PlattCertificates.Count131072.C027019
import PlattCertificates.Count131072.C027020
import PlattCertificates.Count131072.C027021
import PlattCertificates.Count131072.C027022
import PlattCertificates.Count131072.C027023
import PlattCertificates.Count131072.C027024
import PlattCertificates.Count131072.C027025
import PlattCertificates.Count131072.C027026
import PlattCertificates.Count131072.C027027
import PlattCertificates.Count131072.C027028
import PlattCertificates.Count131072.C027029
import PlattCertificates.Count131072.C027030
import PlattCertificates.Count131072.C027031
import PlattCertificates.Count131072.C027032
import PlattCertificates.Count131072.C027033
import PlattCertificates.Count131072.C027034
import PlattCertificates.Count131072.C027035
import PlattCertificates.Count131072.C027036
import PlattCertificates.Count131072.C027037
import PlattCertificates.Count131072.C027038
import PlattCertificates.Count131072.C027039
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000219
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts27008 : List PrefixCut := [⟨109,400452678,400452904⟩,
⟨128,468676097,468676362⟩]
theorem checked27008 : checkPrefixCuts (2^48) 3543924737 9 Manual.Count131072.C027008.packed 128 cuts27008 = true := by
 decide +kernel
def pointBounds27008 : List (Nat × Nat × Nat) := [(3544036352,103888039258298,103888421829118)]
theorem point_links_checked27008 : (cuts27008.take 1).map (fun c => (3543924737-1+2*2^9*c.k,103887638805620+c.lower,103888021376214+c.upper)) = pointBounds27008 := by
 decide +kernel
def cuts27009 : List PrefixCut := [⟨90,335711088,335711275⟩,
⟨128,473662216,473662483⟩]
theorem checked27009 : checkPrefixCuts (2^48) 3544055809 9 Manual.Count131072.C027009.packed 128 cuts27009 = true := by
 decide +kernel
def pointBounds27009 : List (Nat × Nat × Nat) := [(3544147968,103888443192805,103888825763851)]
theorem point_links_checked27009 : (cuts27009.take 1).map (fun c => (3544055809-1+2*2^9*c.k,103888107481717+c.lower,103888490052576+c.upper)) = pointBounds27009 := by
 decide +kernel
def cuts27010 : List PrefixCut := [⟨71,262158623,262158772⟩,
⟨128,475709508,475709776⟩]
theorem checked27010 : checkPrefixCuts (2^48) 3544186881 9 Manual.Count131072.C027010.packed 128 cuts27010 = true := by
 decide +kernel
def pointBounds27010 : List (Nat × Nat × Nat) := [(3544259584,103888843302556,103889225873831)]
theorem point_links_checked27010 : (cuts27010.take 1).map (fun c => (3544186881-1+2*2^9*c.k,103888581143933+c.lower,103888963715059+c.upper)) = pointBounds27010 := by
 decide +kernel
def cuts27011 : List PrefixCut := [⟨52,191152449,191152552⟩,
⟨128,473309504,473309764⟩]
theorem checked27011 : checkPrefixCuts (2^48) 3544317953 9 Manual.Count131072.C027011.packed 128 cuts27011 = true := by
 decide +kernel
def pointBounds27011 : List (Nat × Nat × Nat) := [(3544371200,103889248005890,103889630577387)]
theorem point_links_checked27011 : (cuts27011.take 1).map (fun c => (3544317953-1+2*2^9*c.k,103889056853441+c.lower,103889439424835+c.upper)) = pointBounds27011 := by
 decide +kernel
def cuts27012 : List PrefixCut := [⟨33,123089373,123089438⟩,
⟨128,474800799,474801059⟩]
theorem checked27012 : checkPrefixCuts (2^48) 3544449025 9 Manual.Count131072.C027012.packed 128 cuts27012 = true := by
 decide +kernel
def pointBounds27012 : List (Nat × Nat × Nat) := [(3544482816,103889653252318,103890035824037)]
theorem point_links_checked27012 : (cuts27012.take 1).map (fun c => (3544449025-1+2*2^9*c.k,103889530162945+c.lower,103889912734599+c.upper)) = pointBounds27012 := by
 decide +kernel
def cuts27013 : List PrefixCut := [⟨14,52966324,52966353⟩,
⟨123,463031154,463031411⟩,
⟨128,481215371,481215639⟩]
theorem checked27013 : checkPrefixCuts (2^48) 3544580097 9 Manual.Count131072.C027013.packed 128 cuts27013 = true := by
 decide +kernel
def pointBounds27013 : List (Nat × Nat × Nat) := [(3544594432,103890057930068,103890440502011),(3544706048,103890467994898,103890850567069)]
theorem point_links_checked27013 : (cuts27013.take 2).map (fun c => (3544580097-1+2*2^9*c.k,103890004963744+c.lower,103890387535658+c.upper)) = pointBounds27013 := by
 decide +kernel
def cuts27014 : List PrefixCut := [⟨104,385594608,385594827⟩,
⟨128,471668913,471669182⟩]
theorem checked27014 : checkPrefixCuts (2^48) 3544711169 9 Manual.Count131072.C027014.packed 128 cuts27014 = true := by
 decide +kernel
def pointBounds27014 : List (Nat × Nat × Nat) := [(3544817664,103890871773723,103891254346124)]
theorem point_links_checked27014 : (cuts27014.take 1).map (fun c => (3544711169-1+2*2^9*c.k,103890486179115+c.lower,103890868751297+c.upper)) = pointBounds27014 := by
 decide +kernel
def cuts27015 : List PrefixCut := [⟨85,311021872,311022047⟩,
⟨128,470539735,470540001⟩]
theorem checked27015 : checkPrefixCuts (2^48) 3544842241 9 Manual.Count131072.C027015.packed 128 cuts27015 = true := by
 decide +kernel
def pointBounds27015 : List (Nat × Nat × Nat) := [(3544929280,103891268869900,103891651442526)]
theorem point_links_checked27015 : (cuts27015.take 1).map (fun c => (3544842241-1+2*2^9*c.k,103890957848028+c.lower,103891340420479+c.upper)) = pointBounds27015 := by
 decide +kernel
def cuts27016 : List PrefixCut := [⟨66,243917921,243918060⟩,
⟨128,478462307,478462576⟩]
theorem checked27016 : checkPrefixCuts (2^48) 3544973313 9 Manual.Count131072.C027016.packed 128 cuts27016 = true := by
 decide +kernel
def pointBounds27016 : List (Nat × Nat × Nat) := [(3545040896,103891672305684,103892054878540)]
theorem point_links_checked27016 : (cuts27016.take 1).map (fun c => (3544973313-1+2*2^9*c.k,103891428387763+c.lower,103891810960480+c.upper)) = pointBounds27016 := by
 decide +kernel
def cuts27017 : List PrefixCut := [⟨47,168640633,168640729⟩,
⟨128,467805446,467805712⟩]
theorem checked27017 : checkPrefixCuts (2^48) 3545104385 9 Manual.Count131072.C027017.packed 128 cuts27017 = true := by
 decide +kernel
def pointBounds27017 : List (Nat × Nat × Nat) := [(3545152512,103892075490703,103892458063785)]
theorem point_links_checked27017 : (cuts27017.take 1).map (fun c => (3545104385-1+2*2^9*c.k,103891906850070+c.lower,103892289423056+c.upper)) = pointBounds27017 := by
 decide +kernel
def cuts27018 : List PrefixCut := [⟨28,105357083,105357142⟩,
⟨128,481285185,481285453⟩]
theorem checked27018 : checkPrefixCuts (2^48) 3545235457 9 Manual.Count131072.C027018.packed 128 cuts27018 = true := by
 decide +kernel
def pointBounds27018 : List (Nat × Nat × Nat) := [(3545264128,103892480012599,103892862585910)]
theorem point_links_checked27018 : (cuts27018.take 1).map (fun c => (3545235457-1+2*2^9*c.k,103892374655516+c.lower,103892757228768+c.upper)) = pointBounds27018 := by
 decide +kernel
def cuts27019 : List PrefixCut := [⟨9,34773795,34773814⟩,
⟨118,437444259,437444501⟩,
⟨128,472772591,472772853⟩]
theorem checked27019 : checkPrefixCuts (2^48) 3545366529 9 Manual.Count131072.C027019.packed 128 cuts27019 = true := by
 decide +kernel
def pointBounds27019 : List (Nat × Nat × Nat) := [(3545375744,103892890714496,103893273288035),(3545487360,103893293384960,103893675958722)]
theorem point_links_checked27019 : (cuts27019.take 2).map (fun c => (3545366529-1+2*2^9*c.k,103892855940701+c.lower,103893238514221+c.upper)) = pointBounds27019 := by
 decide +kernel
def cuts27020 : List PrefixCut := [⟨99,367726356,367726555⟩,
⟨128,476724427,476724684⟩]
theorem checked27020 : checkPrefixCuts (2^48) 3545497601 9 Manual.Count131072.C027020.packed 128 cuts27020 = true := by
 decide +kernel
def pointBounds27020 : List (Nat × Nat × Nat) := [(3545598976,103893696439648,103894079013629)]
theorem point_links_checked27020 : (cuts27020.take 1).map (fun c => (3545497601-1+2*2^9*c.k,103893328713292+c.lower,103893711287074+c.upper)) = pointBounds27020 := by
 decide +kernel
def cuts27021 : List PrefixCut := [⟨80,290074772,290074938⟩,
⟨128,468450780,468451043⟩]
theorem checked27021 : checkPrefixCuts (2^48) 3545628673 9 Manual.Count131072.C027021.packed 128 cuts27021 = true := by
 decide +kernel
def pointBounds27021 : List (Nat × Nat × Nat) := [(3545710592,103894095512491,103894478086696)]
theorem point_links_checked27021 : (cuts27021.take 1).map (fun c => (3545628673-1+2*2^9*c.k,103893805437719+c.lower,103894188011758+c.upper)) = pointBounds27021 := by
 decide +kernel
def cuts27022 : List PrefixCut := [⟨61,226241047,226241175⟩,
⟨128,471211924,471212190⟩]
theorem checked27022 : checkPrefixCuts (2^48) 3545759745 9 Manual.Count131072.C027022.packed 128 cuts27022 = true := by
 decide +kernel
def pointBounds27022 : List (Nat × Nat × Nat) := [(3545822208,103894500129546,103894882703976)]
theorem point_links_checked27022 : (cuts27022.take 1).map (fun c => (3545759745-1+2*2^9*c.k,103894273888499+c.lower,103894656462801+c.upper)) = pointBounds27022 := by
 decide +kernel
def cuts27023 : List PrefixCut := [⟨42,156537566,156537653⟩,
⟨128,472226395,472226657⟩]
theorem checked27023 : checkPrefixCuts (2^48) 3545890817 9 Manual.Count131072.C027023.packed 128 cuts27023 = true := by
 decide +kernel
def pointBounds27023 : List (Nat × Nat × Nat) := [(3545933824,103894901637989,103895284212644)]
theorem point_links_checked27023 : (cuts27023.take 1).map (fun c => (3545890817-1+2*2^9*c.k,103894745100423+c.lower,103895127674991+c.upper)) = pointBounds27023 := by
 decide +kernel
def cuts27024 : List PrefixCut := [⟨23,83901905,83901955⟩,
⟨128,471653316,471653581⟩]
theorem checked27024 : checkPrefixCuts (2^48) 3546021889 9 Manual.Count131072.C027024.packed 128 cuts27024 = true := by
 decide +kernel
def pointBounds27024 : List (Nat × Nat × Nat) := [(3546045440,103895301228723,103895683803603)]
theorem point_links_checked27024 : (cuts27024.take 1).map (fun c => (3546021889-1+2*2^9*c.k,103895217326818+c.lower,103895599901648+c.upper)) = pointBounds27024 := by
 decide +kernel
def cuts27025 : List PrefixCut := [⟨4,15398688,15398696⟩,
⟨113,411313033,411313263⟩,
⟨128,467587752,467588013⟩]
theorem checked27025 : checkPrefixCuts (2^48) 3546152961 9 Manual.Count131072.C027025.packed 128 cuts27025 = true := by
 decide +kernel
def pointBounds27025 : List (Nat × Nat × Nat) := [(3546157056,103895704378822,103896086953925),(3546268672,103896100293167,103896482868492)]
theorem point_links_checked27025 : (cuts27025.take 2).map (fun c => (3546152961-1+2*2^9*c.k,103895688980134+c.lower,103896071555229+c.upper)) = pointBounds27025 := by
 decide +kernel
def cuts27026 : List PrefixCut := [⟨94,347167463,347167659⟩,
⟨128,476618702,476618967⟩]
theorem checked27026 : checkPrefixCuts (2^48) 3546284033 9 Manual.Count131072.C027026.packed 128 cuts27026 = true := by
 decide +kernel
def pointBounds27026 : List (Nat × Nat × Nat) := [(3546380288,103896503735349,103896886310901)]
theorem point_links_checked27026 : (cuts27026.take 1).map (fun c => (3546284033-1+2*2^9*c.k,103896156567886+c.lower,103896539143242+c.upper)) = pointBounds27026 := by
 decide +kernel
def cuts27027 : List PrefixCut := [⟨75,278343570,278343724⟩,
⟨128,473902700,473902964⟩]
theorem checked27027 : checkPrefixCuts (2^48) 3546415105 9 Manual.Count131072.C027027.packed 128 cuts27027 = true := by
 decide +kernel
def pointBounds27027 : List (Nat × Nat × Nat) := [(3546491904,103896911530158,103897294105933)]
theorem point_links_checked27027 : (cuts27027.take 1).map (fun c => (3546415105-1+2*2^9*c.k,103896633186588+c.lower,103897015762209+c.upper)) = pointBounds27027 := by
 decide +kernel
def cuts27028 : List PrefixCut := [⟨56,206984661,206984779⟩,
⟨128,473329594,473329862⟩]
theorem checked27028 : checkPrefixCuts (2^48) 3546546177 9 Manual.Count131072.C027028.packed 128 cuts27028 = true := by
 decide +kernel
def pointBounds27028 : List (Nat × Nat × Nat) := [(3546603520,103897314073949,103897696649952)]
theorem point_links_checked27028 : (cuts27028.take 1).map (fun c => (3546546177-1+2*2^9*c.k,103897107089288+c.lower,103897489665173+c.upper)) = pointBounds27028 := by
 decide +kernel
def cuts27029 : List PrefixCut := [⟨37,138805119,138805197⟩,
⟨128,470534498,470534764⟩]
theorem checked27029 : checkPrefixCuts (2^48) 3546677249 9 Manual.Count131072.C027029.packed 128 cuts27029 = true := by
 decide +kernel
def pointBounds27029 : List (Nat × Nat × Nat) := [(3546715136,103897719224001,103898101800232)]
theorem point_links_checked27029 : (cuts27029.take 1).map (fun c => (3546677249-1+2*2^9*c.k,103897580418882+c.lower,103897962995035+c.upper)) = pointBounds27029 := by
 decide +kernel
def cuts27030 : List PrefixCut := [⟨18,68011388,68011425⟩,
⟨127,467660264,467660528⟩,
⟨128,471548764,471549030⟩]
theorem checked27030 : checkPrefixCuts (2^48) 3546808321 9 Manual.Count131072.C027030.packed 128 cuts27030 = true := by
 decide +kernel
def pointBounds27030 : List (Nat × Nat × Nat) := [(3546826752,103898118964768,103898501541224),(3546938368,103898518613644,103898901190327)]
theorem point_links_checked27030 : (cuts27030.take 2).map (fun c => (3546808321-1+2*2^9*c.k,103898050953380+c.lower,103898433529799+c.upper)) = pointBounds27030 := by
 decide +kernel
def cuts27031 : List PrefixCut := [⟨108,398604592,398604817⟩,
⟨128,475340309,475340575⟩]
theorem checked27031 : checkPrefixCuts (2^48) 3546939393 9 Manual.Count131072.C027031.packed 128 cuts27031 = true := by
 decide +kernel
def pointBounds27031 : List (Nat × Nat × Nat) := [(3547049984,103898921106736,103899303683646)]
theorem point_links_checked27031 : (cuts27031.take 1).map (fun c => (3546939393-1+2*2^9*c.k,103898522502144+c.lower,103898905078829+c.upper)) = pointBounds27031 := by
 decide +kernel
def cuts27032 : List PrefixCut := [⟨89,327014391,327014573⟩,
⟨128,470085516,470085778⟩]
theorem checked27032 : checkPrefixCuts (2^48) 3547070465 9 Manual.Count131072.C027032.packed 128 cuts27032 = true := by
 decide +kernel
def pointBounds27032 : List (Nat × Nat × Nat) := [(3547161600,103899324856844,103899707433977)]
theorem point_links_checked27032 : (cuts27032.take 1).map (fun c => (3547070465-1+2*2^9*c.k,103898997842453+c.lower,103899380419404+c.upper)) = pointBounds27032 := by
 decide +kernel
def cuts27033 : List PrefixCut := [⟨70,256698719,256698863⟩,
⟨128,468005090,468005350⟩]
theorem checked27033 : checkPrefixCuts (2^48) 3547201537 9 Manual.Count131072.C027033.packed 128 cuts27033 = true := by
 decide +kernel
def pointBounds27033 : List (Nat × Nat × Nat) := [(3547273216,103899724626688,103900107204045)]
theorem point_links_checked27033 : (cuts27033.take 1).map (fun c => (3547201537-1+2*2^9*c.k,103899467927969+c.lower,103899850505182+c.upper)) = pointBounds27033 := by
 decide +kernel
def cuts27034 : List PrefixCut := [⟨51,188371533,188371642⟩,
⟨128,477668027,477668298⟩]
theorem checked27034 : checkPrefixCuts (2^48) 3547332609 9 Manual.Count131072.C027034.packed 128 cuts27034 = true := by
 decide +kernel
def pointBounds27034 : List (Nat × Nat × Nat) := [(3547384832,103900124304592,103900506882174)]
theorem point_links_checked27034 : (cuts27034.take 1).map (fun c => (3547332609-1+2*2^9*c.k,103899935933059+c.lower,103900318510532+c.upper)) = pointBounds27034 := by
 decide +kernel
def cuts27035 : List PrefixCut := [⟨32,119017537,119017598⟩,
⟨128,472255085,472255344⟩]
theorem checked27035 : checkPrefixCuts (2^48) 3547463681 9 Manual.Count131072.C027035.packed 128 cuts27035 = true := by
 decide +kernel
def pointBounds27035 : List (Nat × Nat × Nat) := [(3547496448,103900532618623,103900915196428)]
theorem point_links_checked27035 : (cuts27035.take 1).map (fun c => (3547463681-1+2*2^9*c.k,103900413601086+c.lower,103900796178830+c.upper)) = pointBounds27035 := by
 decide +kernel
def cuts27036 : List PrefixCut := [⟨13,50620397,50620423⟩,
⟨122,450498601,450498850⟩,
⟨128,474538499,474538761⟩]
theorem checked27036 : checkPrefixCuts (2^48) 3547594753 9 Manual.Count131072.C027036.packed 128 cuts27036 = true := by
 decide +kernel
def pointBounds27036 : List (Nat × Nat × Nat) := [(3547608064,103900936476568,103901319054597),(3547719680,103901336354772,103901718933024)]
theorem point_links_checked27036 : (cuts27036.take 2).map (fun c => (3547594753-1+2*2^9*c.k,103900885856171+c.lower,103901268434174+c.upper)) = pointBounds27036 := by
 decide +kernel
def cuts27037 : List PrefixCut := [⟨103,378285266,378285484⟩,
⟨128,469919361,469919630⟩]
theorem checked27037 : checkPrefixCuts (2^48) 3547725825 9 Manual.Count131072.C027037.packed 128 cuts27037 = true := by
 decide +kernel
def pointBounds27037 : List (Nat × Nat × Nat) := [(3547831296,103901738679936,103902121258419)]
theorem point_links_checked27037 : (cuts27037.take 1).map (fun c => (3547725825-1+2*2^9*c.k,103901360394670+c.lower,103901742972935+c.upper)) = pointBounds27037 := by
 decide +kernel
def cuts27038 : List PrefixCut := [⟨84,315438452,315438625⟩,
⟨128,478549502,478549763⟩]
theorem checked27038 : checkPrefixCuts (2^48) 3547856897 9 Manual.Count131072.C027038.packed 128 cuts27038 = true := by
 decide +kernel
def pointBounds27038 : List (Nat × Nat × Nat) := [(3547942912,103902145752483,103902528331190)]
theorem point_links_checked27038 : (cuts27038.take 1).map (fun c => (3547856897-1+2*2^9*c.k,103901830314031+c.lower,103902212892565+c.upper)) = pointBounds27038 := by
 decide +kernel
def cuts27039 : List PrefixCut := [⟨65,240934084,240934222⟩,
⟨128,477738488,477738756⟩]
theorem checked27039 : checkPrefixCuts (2^48) 3547987969 9 Manual.Count131072.C027039.packed 128 cuts27039 = true := by
 decide +kernel
def pointBounds27039 : List (Nat × Nat × Nat) := [(3548054528,103902549797617,103902932376550)]
theorem point_links_checked27039 : (cuts27039.take 1).map (fun c => (3547987969-1+2*2^9*c.k,103902308863533+c.lower,103902691442328+c.upper)) = pointBounds27039 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000219
