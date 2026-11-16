import PlattAssemblyKernel
import PlattCertificates.Count131072.C022944
import PlattCertificates.Count131072.C022945
import PlattCertificates.Count131072.C022946
import PlattCertificates.Count131072.C022947
import PlattCertificates.Count131072.C022948
import PlattCertificates.Count131072.C022949
import PlattCertificates.Count131072.C022950
import PlattCertificates.Count131072.C022951
import PlattCertificates.Count131072.C022952
import PlattCertificates.Count131072.C022953
import PlattCertificates.Count131072.C022954
import PlattCertificates.Count131072.C022955
import PlattCertificates.Count131072.C022956
import PlattCertificates.Count131072.C022957
import PlattCertificates.Count131072.C022958
import PlattCertificates.Count131072.C022959
import PlattCertificates.Count131072.C022960
import PlattCertificates.Count131072.C022961
import PlattCertificates.Count131072.C022962
import PlattCertificates.Count131072.C022963
import PlattCertificates.Count131072.C022964
import PlattCertificates.Count131072.C022965
import PlattCertificates.Count131072.C022966
import PlattCertificates.Count131072.C022967
import PlattCertificates.Count131072.C022968
import PlattCertificates.Count131072.C022969
import PlattCertificates.Count131072.C022970
import PlattCertificates.Count131072.C022971
import PlattCertificates.Count131072.C022972
import PlattCertificates.Count131072.C022973
import PlattCertificates.Count131072.C022974
import PlattCertificates.Count131072.C022975
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000092
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts22944 : List PrefixCut := [⟨20,87772242,87772294⟩,
⟨112,498209492,498209777⟩,
⟨128,569901509,569901837⟩]
theorem checked22944 : checkPrefixCuts (2^48) 3011248129 9 Manual.Count131072.C022944.packed 128 cuts22944 = true := by
 decide +kernel
def pointBounds22944 : List (Nat × Nat × Nat) := [(3011268608,101794910129218,101795291522803),(3011362816,101795320566468,101795701960286)]
theorem point_links_checked22944 : (cuts22944.take 2).map (fun c => (3011248129-1+2*2^9*c.k,101794822356976+c.lower,101795203750509+c.upper)) = pointBounds22944 := by
 decide +kernel
def cuts22945 : List PrefixCut := [⟨76,330226770,330226956⟩,
⟨128,563801256,563801573⟩]
theorem checked22945 : checkPrefixCuts (2^48) 3011379201 9 Manual.Count131072.C022945.packed 128 cuts22945 = true := by
 decide +kernel
def pointBounds22945 : List (Nat × Nat × Nat) := [(3011457024,101795722485255,101796103879302)]
theorem point_links_checked22945 : (cuts22945.take 1).map (fun c => (3011379201-1+2*2^9*c.k,101795392258485+c.lower,101795773652346+c.upper)) = pointBounds22945 := by
 decide +kernel
def cuts22946 : List PrefixCut := [⟨40,168892575,168892671⟩,
⟨128,558542712,558543030⟩]
theorem checked22946 : checkPrefixCuts (2^48) 3011510273 9 Manual.Count131072.C022946.packed 128 cuts22946 = true := by
 decide +kernel
def pointBounds22946 : List (Nat × Nat × Nat) := [(3011551232,101796124952316,101796506346590)]
theorem point_links_checked22946 : (cuts22946.take 1).map (fun c => (3011510273-1+2*2^9*c.k,101795956059741+c.lower,101796337453919+c.upper)) = pointBounds22946 := by
 decide +kernel
def cuts22947 : List PrefixCut := [⟨4,15140879,15140889⟩,
⟨96,419451881,419452120⟩,
⟨128,557116599,557116917⟩]
theorem checked22947 : checkPrefixCuts (2^48) 3011641345 9 Manual.Count131072.C022947.packed 128 cuts22947 = true := by
 decide +kernel
def pointBounds22947 : List (Nat × Nat × Nat) := [(3011645440,101796529743332,101796911137838),(3011739648,101796934054334,101797315449069)]
theorem point_links_checked22947 : (cuts22947.take 2).map (fun c => (3011641345-1+2*2^9*c.k,101796514602453+c.lower,101796895996949+c.upper)) = pointBounds22947 := by
 decide +kernel
def cuts22948 : List PrefixCut := [⟨60,261680358,261680502⟩,
⟨128,561484754,561485068⟩]
theorem checked22948 : checkPrefixCuts (2^48) 3011772417 9 Manual.Count131072.C022948.packed 128 cuts22948 = true := by
 decide +kernel
def pointBounds22948 : List (Nat × Nat × Nat) := [(3011833856,101797333399410,101797714794368)]
theorem point_links_checked22948 : (cuts22948.take 1).map (fun c => (3011772417-1+2*2^9*c.k,101797071719052+c.lower,101797453113866+c.upper)) = pointBounds22948 := by
 decide +kernel
def cuts22949 : List PrefixCut := [⟨24,104574769,104574827⟩,
⟨116,506044324,506044611⟩,
⟨128,561273441,561273757⟩]
theorem checked22949 : checkPrefixCuts (2^48) 3011903489 9 Manual.Count131072.C022949.packed 128 cuts22949 = true := by
 decide +kernel
def pointBounds22949 : List (Nat × Nat × Nat) := [(3011928064,101797737778575,101798119173761),(3012022272,101798139248130,101798520643545)]
theorem point_links_checked22949 : (cuts22949.take 2).map (fun c => (3011903489-1+2*2^9*c.k,101797633203806+c.lower,101798014598934+c.upper)) = pointBounds22949 := by
 decide +kernel
def cuts22950 : List PrefixCut := [⟨80,350152738,350152947⟩,
⟨128,562931089,562931421⟩]
theorem checked22950 : checkPrefixCuts (2^48) 3012034561 9 Manual.Count131072.C022950.packed 128 cuts22950 = true := by
 decide +kernel
def pointBounds22950 : List (Nat × Nat × Nat) := [(3012116480,101798544629985,101798926025638)]
theorem point_links_checked22950 : (cuts22950.take 1).map (fun c => (3012034561-1+2*2^9*c.k,101798194477247+c.lower,101798575872691+c.upper)) = pointBounds22950 := by
 decide +kernel
def cuts22951 : List PrefixCut := [⟨44,192403945,192404053⟩,
⟨128,562626239,562626555⟩]
theorem checked22951 : checkPrefixCuts (2^48) 3012165633 9 Manual.Count131072.C022951.packed 128 cuts22951 = true := by
 decide +kernel
def pointBounds22951 : List (Nat × Nat × Nat) := [(3012210688,101798949812281,101799331208165)]
theorem point_links_checked22951 : (cuts22951.take 1).map (fun c => (3012165633-1+2*2^9*c.k,101798757408336+c.lower,101799138804112+c.upper)) = pointBounds22951 := by
 decide +kernel
def cuts22952 : List PrefixCut := [⟨8,35321013,35321031⟩,
⟨100,436927111,436927365⟩,
⟨128,560265709,560266032⟩]
theorem checked22952 : checkPrefixCuts (2^48) 3012296705 9 Manual.Count131072.C022952.packed 128 cuts22952 = true := by
 decide +kernel
def pointBounds22952 : List (Nat × Nat × Nat) := [(3012304896,101799355355588,101799736751698),(3012399104,101799756961686,101800138358032)]
theorem point_links_checked22952 : (cuts22952.take 2).map (fun c => (3012296705-1+2*2^9*c.k,101799320034575+c.lower,101799701430667+c.upper)) = pointBounds22952 := by
 decide +kernel
def cuts22953 : List PrefixCut := [⟨64,277787833,277787995⟩,
⟨128,564726212,564726540⟩]
theorem checked22953 : checkPrefixCuts (2^48) 3012427777 9 Manual.Count131072.C022953.packed 128 cuts22953 = true := by
 decide +kernel
def pointBounds22953 : List (Nat × Nat × Nat) := [(3012493312,101800158088117,101800539484694)]
theorem point_links_checked22953 : (cuts22953.take 1).map (fun c => (3012427777-1+2*2^9*c.k,101799880300284+c.lower,101800261696699+c.upper)) = pointBounds22953 := by
 decide +kernel
def cuts22954 : List PrefixCut := [⟨28,123518931,123518999⟩,
⟨120,522471302,522471593⟩,
⟨128,558348379,558348691⟩]
theorem checked22954 : checkPrefixCuts (2^48) 3012558849 9 Manual.Count131072.C022954.packed 128 cuts22954 = true := by
 decide +kernel
def pointBounds22954 : List (Nat × Nat × Nat) := [(3012587520,101800568545427,101800949942238),(3012681728,101800967497798,101801348894832)]
theorem point_links_checked22954 : (cuts22954.take 2).map (fun c => (3012558849-1+2*2^9*c.k,101800445026496+c.lower,101800826423239+c.upper)) = pointBounds22954 := by
 decide +kernel
def cuts22955 : List PrefixCut := [⟨84,372499103,372499313⟩,
⟨128,559819007,559819326⟩]
theorem checked22955 : checkPrefixCuts (2^48) 3012689921 9 Manual.Count131072.C022955.packed 128 cuts22955 = true := by
 decide +kernel
def pointBounds22955 : List (Nat × Nat × Nat) := [(3012775936,101801375873978,101801757271243)]
theorem point_links_checked22955 : (cuts22955.take 1).map (fun c => (3012689921-1+2*2^9*c.k,101801003374875+c.lower,101801384771930+c.upper)) = pointBounds22955 := by
 decide +kernel
def cuts22956 : List PrefixCut := [⟨48,213849652,213849773⟩,
⟨128,568482996,568483314⟩]
theorem checked22956 : checkPrefixCuts (2^48) 3012820993 9 Manual.Count131072.C022956.packed 128 cuts22956 = true := by
 decide +kernel
def pointBounds22956 : List (Nat × Nat × Nat) := [(3012870144,101801777043534,101802158441029)]
theorem point_links_checked22956 : (cuts22956.take 1).map (fun c => (3012820993-1+2*2^9*c.k,101801563193882+c.lower,101801944591256+c.upper)) = pointBounds22956 := by
 decide +kernel
def cuts22957 : List PrefixCut := [⟨12,51755480,51755509⟩,
⟨104,455328978,455329238⟩,
⟨128,561732025,561732345⟩]
theorem checked22957 : checkPrefixCuts (2^48) 3012952065 9 Manual.Count131072.C022957.packed 128 cuts22957 = true := by
 decide +kernel
def pointBounds22957 : List (Nat × Nat × Nat) := [(3012964352,101802183432358,101802564830079),(3013058560,101802587005856,101802968403808)]
theorem point_links_checked22957 : (cuts22957.take 2).map (fun c => (3012952065-1+2*2^9*c.k,101802131676878+c.lower,101802513074570+c.upper)) = pointBounds22957 := by
 decide +kernel
def cuts22958 : List PrefixCut := [⟨68,299586693,299586865⟩,
⟨128,560866930,560867250⟩]
theorem checked22958 : checkPrefixCuts (2^48) 3013083137 9 Manual.Count131072.C022958.packed 128 cuts22958 = true := by
 decide +kernel
def pointBounds22958 : List (Nat × Nat × Nat) := [(3013152768,101802992995596,101803374393780)]
theorem point_links_checked22958 : (cuts22958.take 1).map (fun c => (3013083137-1+2*2^9*c.k,101802693408903+c.lower,101803074806915+c.upper)) = pointBounds22958 := by
 decide +kernel
def cuts22959 : List PrefixCut := [⟨32,143295533,143295612⟩,
⟨124,546177232,546177542⟩,
⟨128,561683209,561683528⟩]
theorem checked22959 : checkPrefixCuts (2^48) 3013214209 9 Manual.Count131072.C022959.packed 128 cuts22959 = true := by
 decide +kernel
def pointBounds22959 : List (Nat × Nat × Nat) := [(3013246976,101803397571366,101803778969777),(3013341184,101803800453065,101804181851707)]
theorem point_links_checked22959 : (cuts22959.take 2).map (fun c => (3013214209-1+2*2^9*c.k,101803254275833+c.lower,101803635674165+c.upper)) = pointBounds22959 := by
 decide +kernel
def cuts22960 : List PrefixCut := [⟨88,381104831,381105056⟩,
⟨128,555960865,555961193⟩]
theorem checked22960 : checkPrefixCuts (2^48) 3013345281 9 Manual.Count131072.C022960.packed 128 cuts22960 = true := by
 decide +kernel
def pointBounds22960 : List (Nat × Nat × Nat) := [(3013435392,101804197063873,101804578462749)]
theorem point_links_checked22960 : (cuts22960.take 1).map (fun c => (3013345281-1+2*2^9*c.k,101803815959042+c.lower,101804197357693+c.upper)) = pointBounds22960 := by
 decide +kernel
def cuts22961 : List PrefixCut := [⟨52,225198407,225198534⟩,
⟨128,560980528,560980843⟩]
theorem checked22961 : checkPrefixCuts (2^48) 3013476353 9 Manual.Count131072.C022961.packed 128 cuts22961 = true := by
 decide +kernel
def pointBounds22961 : List (Nat × Nat × Nat) := [(3013529600,101804597118314,101804978517420)]
theorem point_links_checked22961 : (cuts22961.take 1).map (fun c => (3013476353-1+2*2^9*c.k,101804371919907+c.lower,101804753318886+c.upper)) = pointBounds22961 := by
 decide +kernel
def cuts22962 : List PrefixCut := [⟨16,70144200,70144241⟩,
⟨108,477365357,477365625⟩,
⟨128,565252468,565252789⟩]
theorem checked22962 : checkPrefixCuts (2^48) 3013607425 9 Manual.Count131072.C022962.packed 128 cuts22962 = true := by
 decide +kernel
def pointBounds22962 : List (Nat × Nat × Nat) := [(3013623808,101805003044635,101805384443970),(3013718016,101805410265792,101805791665354)]
theorem point_links_checked22962 : (cuts22962.take 2).map (fun c => (3013607425-1+2*2^9*c.k,101804932900435+c.lower,101805314299729+c.upper)) = pointBounds22962 := by
 decide +kernel
def cuts22963 : List PrefixCut := [⟨72,316052434,316052614⟩,
⟨128,561025117,561025434⟩]
theorem checked22963 : checkPrefixCuts (2^48) 3013738497 9 Manual.Count131072.C022963.packed 128 cuts22963 = true := by
 decide +kernel
def pointBounds22963 : List (Nat × Nat × Nat) := [(3013812224,101805814205337,101806195605132)]
theorem point_links_checked22963 : (cuts22963.take 1).map (fun c => (3013738497-1+2*2^9*c.k,101805498152903+c.lower,101805879552518+c.upper)) = pointBounds22963 := by
 decide +kernel
def cuts22964 : List PrefixCut := [⟨36,155405321,155405412⟩,
⟨128,557358441,557358767⟩]
theorem checked22964 : checkPrefixCuts (2^48) 3013869569 9 Manual.Count131072.C022964.packed 128 cuts22964 = true := by
 decide +kernel
def pointBounds22964 : List (Nat × Nat × Nat) := [(3013906432,101806214583341,101806595983364),(3014000640,101806616536461,101806997936719)]
theorem point_links_checked22964 : (cuts22964.take 2).map (fun c => (3013869569-1+2*2^9*c.k,101806059178020+c.lower,101806440577952+c.upper)) = pointBounds22964 := by
 decide +kernel
def cuts22965 : List PrefixCut := [⟨92,405115637,405115868⟩,
⟨128,565272011,565272328⟩]
theorem checked22965 : checkPrefixCuts (2^48) 3014000641 9 Manual.Count131072.C022965.packed 128 cuts22965 = true := by
 decide +kernel
def pointBounds22965 : List (Nat × Nat × Nat) := [(3014094848,101807021652098,101807403052587)]
theorem point_links_checked22965 : (cuts22965.take 1).map (fun c => (3014000641-1+2*2^9*c.k,101806616536461+c.lower,101806997936719+c.upper)) = pointBounds22965 := by
 decide +kernel
def cuts22966 : List PrefixCut := [⟨56,245880552,245880695⟩,
⟨128,562912935,562913259⟩]
theorem checked22966 : checkPrefixCuts (2^48) 3014131713 9 Manual.Count131072.C022966.packed 128 cuts22966 = true := by
 decide +kernel
def pointBounds22966 : List (Nat × Nat × Nat) := [(3014189056,101807427689024,101807809089742)]
theorem point_links_checked22966 : (cuts22966.take 1).map (fun c => (3014131713-1+2*2^9*c.k,101807181808472+c.lower,101807563209047+c.upper)) = pointBounds22966 := by
 decide +kernel
def cuts22967 : List PrefixCut := [⟨20,86470521,86470568⟩,
⟨112,484731616,484731885⟩,
⟨128,557098944,557099251⟩]
theorem checked22967 : checkPrefixCuts (2^48) 3014262785 9 Manual.Count131072.C022967.packed 128 cuts22967 = true := by
 decide +kernel
def pointBounds22967 : List (Nat × Nat × Nat) := [(3014283264,101807831191928,101808212592874),(3014377472,101808229453023,101808610854191)]
theorem point_links_checked22967 : (cuts22967.take 2).map (fun c => (3014262785-1+2*2^9*c.k,101807744721407+c.lower,101808126122306+c.upper)) = pointBounds22967 := by
 decide +kernel
def cuts22968 : List PrefixCut := [⟨76,333164664,333164856⟩,
⟨128,564451344,564451666⟩]
theorem checked22968 : checkPrefixCuts (2^48) 3014393857 9 Manual.Count131072.C022968.packed 128 cuts22968 = true := by
 decide +kernel
def pointBounds22968 : List (Nat × Nat × Nat) := [(3014471680,101808634985015,101809016386413)]
theorem point_links_checked22968 : (cuts22968.take 1).map (fun c => (3014393857-1+2*2^9*c.k,101808301820351+c.lower,101808683221557+c.upper)) = pointBounds22968 := by
 decide +kernel
def cuts22969 : List PrefixCut := [⟨40,172365186,172365283⟩,
⟨128,560598580,560598891⟩]
theorem checked22969 : checkPrefixCuts (2^48) 3014524929 9 Manual.Count131072.C022969.packed 128 cuts22969 = true := by
 decide +kernel
def pointBounds22969 : List (Nat × Nat × Nat) := [(3014565888,101809038636881,101809420038506)]
theorem point_links_checked22969 : (cuts22969.take 1).map (fun c => (3014524929-1+2*2^9*c.k,101808866271695+c.lower,101809247673223+c.upper)) = pointBounds22969 := by
 decide +kernel
def cuts22970 : List PrefixCut := [⟨4,18113541,18113549⟩,
⟨96,417912073,417912311⟩,
⟨128,557866633,557866949⟩]
theorem checked22970 : checkPrefixCuts (2^48) 3014656001 9 Manual.Count131072.C022970.packed 128 cuts22970 = true := by
 decide +kernel
def pointBounds22970 : List (Nat × Nat × Nat) := [(3014660096,101809444983816,101809826385663),(3014754304,101809844782348,101810226184425)]
theorem point_links_checked22970 : (cuts22970.take 2).map (fun c => (3014656001-1+2*2^9*c.k,101809426870275+c.lower,101809808272114+c.upper)) = pointBounds22970 := by
 decide +kernel
def cuts22971 : List PrefixCut := [⟨61,269261185,269261336⟩,
⟨128,562977324,562977646⟩]
theorem checked22971 : checkPrefixCuts (2^48) 3014787073 9 Manual.Count131072.C022971.packed 128 cuts22971 = true := by
 decide +kernel
def pointBounds22971 : List (Nat × Nat × Nat) := [(3014849536,101810253998093,101810635400399)]
theorem point_links_checked22971 : (cuts22971.take 1).map (fun c => (3014787073-1+2*2^9*c.k,101809984736908+c.lower,101810366139063+c.upper)) = pointBounds22971 := by
 decide +kernel
def cuts22972 : List PrefixCut := [⟨26,114366360,114366424⟩,
⟨119,523089494,523089793⟩,
⟨128,561272421,561272741⟩]
theorem checked22972 : checkPrefixCuts (2^48) 3014918145 9 Manual.Count131072.C022972.packed 128 cuts22972 = true := by
 decide +kernel
def pointBounds22972 : List (Nat × Nat × Nat) := [(3014944768,101810662080592,101811043483133),(3015040000,101811070803726,101811452206502)]
theorem point_links_checked22972 : (cuts22972.take 2).map (fun c => (3014918145-1+2*2^9*c.k,101810547714232+c.lower,101810929116709+c.upper)) = pointBounds22972 := by
 decide +kernel
def cuts22973 : List PrefixCut := [⟨84,370713977,370714190⟩,
⟨128,565262235,565262562⟩]
theorem checked22973 : checkPrefixCuts (2^48) 3015049217 9 Manual.Count131072.C022973.packed 128 cuts22973 = true := by
 decide +kernel
def pointBounds22973 : List (Nat × Nat × Nat) := [(3015135232,101811479700630,101811861103640)]
theorem point_links_checked22973 : (cuts22973.take 1).map (fun c => (3015049217-1+2*2^9*c.k,101811108986653+c.lower,101811490389450+c.upper)) = pointBounds22973 := by
 decide +kernel
def cuts22974 : List PrefixCut := [⟨49,213402280,213402398⟩,
⟨128,555249194,555249504⟩]
theorem checked22974 : checkPrefixCuts (2^48) 3015180289 9 Manual.Count131072.C022974.packed 128 cuts22974 = true := by
 decide +kernel
def pointBounds22974 : List (Nat × Nat × Nat) := [(3015230464,101811887651168,101812269054410)]
theorem point_links_checked22974 : (cuts22974.take 1).map (fun c => (3015180289-1+2*2^9*c.k,101811674248888+c.lower,101812055652012+c.upper)) = pointBounds22974 := by
 decide +kernel
def cuts22975 : List PrefixCut := [⟨14,60116312,60116345⟩,
⟨107,464120441,464120705⟩,
⟨128,556811837,556812156⟩]
theorem checked22975 : checkPrefixCuts (2^48) 3015311361 9 Manual.Count131072.C022975.packed 128 cuts22975 = true := by
 decide +kernel
def pointBounds22975 : List (Nat × Nat × Nat) := [(3015325696,101812289614394,101812671017861),(3015420928,101812693618523,101813075022221)]
theorem point_links_checked22975 : (cuts22975.take 2).map (fun c => (3015311361-1+2*2^9*c.k,101812229498082+c.lower,101812610901516+c.upper)) = pointBounds22975 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000092
