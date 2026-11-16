import PlattAssemblyKernel
import PlattCertificates.Count131072.C017936
import PlattCertificates.Count131072.C017937
import PlattCertificates.Count131072.C017938
import PlattCertificates.Count131072.C017939
import PlattCertificates.Count131072.C017940
import PlattCertificates.Count131072.C017941
import PlattCertificates.Count131072.C017942
import PlattCertificates.Count131072.C017943
import PlattCertificates.Count131072.C017944
import PlattCertificates.Count131072.C017945
import PlattCertificates.Count131072.C017946
import PlattCertificates.Count131072.C017947
import PlattCertificates.Count131072.C017948
import PlattCertificates.Count131072.C017949
import PlattCertificates.Count131072.C017950
import PlattCertificates.Count131072.C017951
import PlattCertificates.Count131072.C017952
import PlattCertificates.Count131072.C017953
import PlattCertificates.Count131072.C017954
import PlattCertificates.Count131072.C017955
import PlattCertificates.Count131072.C017956
import PlattCertificates.Count131072.C017957
import PlattCertificates.Count131072.C017958
import PlattCertificates.Count131072.C017959
import PlattCertificates.Count131072.C017960
import PlattCertificates.Count131072.C017961
import PlattCertificates.Count131072.C017962
import PlattCertificates.Count131072.C017963
import PlattCertificates.Count131072.C017964
import PlattCertificates.Count131072.C017965
import PlattCertificates.Count131072.C017966
import PlattCertificates.Count131072.C017967
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000248
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17936 : List PrefixCut := [⟨36,208698410,208698537⟩,
⟨108,608754124,608754490⟩,
⟨128,724095038,724095473⟩]
theorem checked17936 : checkPrefixCuts (2^48) 2354839553 9 Manual.Count131072.C017936.packed 128 cuts17936 = true := by
 decide +kernel
def pointBounds17936 : List (Nat × Nat × Nat) := [(2354876416,98606100439625,98606479961968),(2354950144,98606500495339,98606880017921)]
theorem point_links_checked17936 : (cuts17936.take 2).map (fun c => (2354839553-1+2*2^9*c.k,98605891741215+c.lower,98606271263431+c.upper)) = pointBounds17936 := by
 decide +kernel
def cuts17937 : List PrefixCut := [⟨52,293786001,293786182⟩,
⟨124,698956006,698956439⟩,
⟨128,722142341,722142788⟩]
theorem checked17937 : checkPrefixCuts (2^48) 2354970625 9 Manual.Count131072.C017937.packed 128 cuts17937 = true := by
 decide +kernel
def pointBounds17937 : List (Nat × Nat × Nat) := [(2355023872,98606909622254,98607289145086),(2355097600,98607314792259,98607694315343)]
theorem point_links_checked17937 : (cuts17937.take 2).map (fun c => (2354970625-1+2*2^9*c.k,98606615836253+c.lower,98606995358904+c.upper)) = pointBounds17937 := by
 decide +kernel
def cuts17938 : List PrefixCut := [⟨68,380297736,380297968⟩,
⟨128,720906873,720907312⟩]
theorem checked17938 : checkPrefixCuts (2^48) 2355101697 9 Manual.Count131072.C017938.packed 128 cuts17938 = true := by
 decide +kernel
def pointBounds17938 : List (Nat × Nat × Nat) := [(2355171328,98607718276330,98608097799660)]
theorem point_links_checked17938 : (cuts17938.take 1).map (fun c => (2355101697-1+2*2^9*c.k,98607337978594+c.lower,98607717501692+c.upper)) = pointBounds17938 := by
 decide +kernel
def cuts17939 : List PrefixCut := [⟨12,68120767,68120808⟩,
⟨84,476957486,476957778⟩,
⟨128,730307935,730308379⟩]
theorem checked17939 : checkPrefixCuts (2^48) 2355232769 9 Manual.Count131072.C017939.packed 128 cuts17939 = true := by
 decide +kernel
def pointBounds17939 : List (Nat × Nat × Nat) := [(2355245056,98608127006234,98608506529812),(2355318784,98608535842953,98608915366782)]
theorem point_links_checked17939 : (cuts17939.take 2).map (fun c => (2355232769-1+2*2^9*c.k,98608058885467+c.lower,98608438409004+c.upper)) = pointBounds17939 := by
 decide +kernel
def cuts17940 : List PrefixCut := [⟨28,157146529,157146624⟩,
⟨100,563567586,563567930⟩,
⟨128,722021752,722022192⟩]
theorem checked17940 : checkPrefixCuts (2^48) 2355363841 9 Manual.Count131072.C017940.packed 128 cuts17940 = true := by
 decide +kernel
def pointBounds17940 : List (Nat × Nat × Nat) := [(2355392512,98608946339931,98609325864007),(2355466240,98609352760988,98609732285313)]
theorem point_links_checked17940 : (cuts17940.take 2).map (fun c => (2355363841-1+2*2^9*c.k,98608789193402+c.lower,98609168717383+c.upper)) = pointBounds17940 := by
 decide +kernel
def cuts17941 : List PrefixCut := [⟨44,246281224,246281376⟩,
⟨116,654469257,654469657⟩,
⟨128,721384103,721384547⟩]
theorem checked17941 : checkPrefixCuts (2^48) 2355494913 9 Manual.Count131072.C017941.packed 128 cuts17941 = true := by
 decide +kernel
def pointBounds17941 : List (Nat × Nat × Nat) := [(2355539968,98609757496378,98610137020951),(2355613696,98610165684411,98610545209232)]
theorem point_links_checked17941 : (cuts17941.take 2).map (fun c => (2355494913-1+2*2^9*c.k,98609511215154+c.lower,98609890739575+c.upper)) = pointBounds17941 := by
 decide +kernel
def cuts17942 : List PrefixCut := [⟨60,337914699,337914905⟩,
⟨128,725406555,725407000⟩]
theorem checked17942 : checkPrefixCuts (2^48) 2355625985 9 Manual.Count131072.C017942.packed 128 cuts17942 = true := by
 decide +kernel
def pointBounds17942 : List (Nat × Nat × Nat) := [(2355687424,98610570513956,98610950039027)]
theorem point_links_checked17942 : (cuts17942.take 1).map (fun c => (2355625985-1+2*2^9*c.k,98610232599257+c.lower,98610612124122+c.upper)) = pointBounds17942 := by
 decide +kernel
def cuts17943 : List PrefixCut := [⟨4,23777263,23777278⟩,
⟨76,434914026,434914289⟩,
⟨128,725605344,725605782⟩]
theorem checked17943 : checkPrefixCuts (2^48) 2355757057 9 Manual.Count131072.C017943.packed 128 cuts17943 = true := by
 decide +kernel
def pointBounds17943 : List (Nat × Nat × Nat) := [(2355761152,98610981783075,98611361308400),(2355834880,98611392919838,98611772445411)]
theorem point_links_checked17943 : (cuts17943.take 2).map (fun c => (2355757057-1+2*2^9*c.k,98610958005812+c.lower,98611337531122+c.upper)) = pointBounds17943 := by
 decide +kernel
def cuts17944 : List PrefixCut := [⟨20,116250793,116250863⟩,
⟨92,533693998,533694320⟩,
⟨128,733569760,733570205⟩]
theorem checked17944 : checkPrefixCuts (2^48) 2355888129 9 Manual.Count131072.C017944.packed 128 cuts17944 = true := by
 decide +kernel
def pointBounds17944 : List (Nat × Nat × Nat) := [(2355908608,98611799861949,98612179387767),(2355982336,98612217305154,98612596831224)]
theorem point_links_checked17944 : (cuts17944.take 2).map (fun c => (2355888129-1+2*2^9*c.k,98611683611156+c.lower,98612063136904+c.upper)) = pointBounds17944 := by
 decide +kernel
def cuts17945 : List PrefixCut := [⟨36,199275305,199275430⟩,
⟨108,608090678,608091058⟩,
⟨128,717400616,717401062⟩]
theorem checked17945 : checkPrefixCuts (2^48) 2356019201 9 Manual.Count131072.C017945.packed 128 cuts17945 = true := by
 decide +kernel
def pointBounds17945 : List (Nat × Nat × Nat) := [(2356056064,98612616456221,98612995982539),(2356129792,98613025271594,98613404798167)]
theorem point_links_checked17945 : (cuts17945.take 2).map (fun c => (2356019201-1+2*2^9*c.k,98612417180916+c.lower,98612796707109+c.upper)) = pointBounds17945 := by
 decide +kernel
def cuts17946 : List PrefixCut := [⟨52,288740990,288741169⟩,
⟨124,701472983,701473414⟩,
⟨128,722736392,722736836⟩]
theorem checked17946 : checkPrefixCuts (2^48) 2356150273 9 Manual.Count131072.C017946.packed 128 cuts17946 = true := by
 decide +kernel
def pointBounds17946 : List (Nat × Nat × Nat) := [(2356203520,98613423322522,98613802849340),(2356277248,98613836054515,98614215581585)]
theorem point_links_checked17946 : (cuts17946.take 2).map (fun c => (2356150273-1+2*2^9*c.k,98613134581532+c.lower,98613514108171+c.upper)) = pointBounds17946 := by
 decide +kernel
def cuts17947 : List PrefixCut := [⟨68,387155241,387155479⟩,
⟨128,734880457,734880904⟩]
theorem checked17947 : checkPrefixCuts (2^48) 2356281345 9 Manual.Count131072.C017947.packed 128 cuts17947 = true := by
 decide +kernel
def pointBounds17947 : List (Nat × Nat × Nat) := [(2356350976,98614244473165,98614624000486)]
theorem point_links_checked17947 : (cuts17947.take 1).map (fun c => (2356281345-1+2*2^9*c.k,98613857317924+c.lower,98614236845007+c.upper)) = pointBounds17947 := by
 decide +kernel
def cuts17948 : List PrefixCut := [⟨12,67608868,67608909⟩,
⟨84,473851889,473852183⟩,
⟨128,725044937,725045391⟩]
theorem checked17948 : checkPrefixCuts (2^48) 2356412417 9 Manual.Count131072.C017948.packed 128 cuts17948 = true := by
 decide +kernel
def pointBounds17948 : List (Nat × Nat × Nat) := [(2356424704,98614659807249,98615039334820),(2356498432,98615066050270,98615445578094)]
theorem point_links_checked17948 : (cuts17948.take 2).map (fun c => (2356412417-1+2*2^9*c.k,98614592198381+c.lower,98614971725911+c.upper)) = pointBounds17948 := by
 decide +kernel
def cuts17949 : List PrefixCut := [⟨28,155515102,155515196⟩,
⟨100,564599270,564599617⟩,
⟨128,723690752,723691195⟩]
theorem checked17949 : checkPrefixCuts (2^48) 2356543489 9 Manual.Count131072.C017949.packed 128 cuts17949 = true := by
 decide +kernel
def pointBounds17949 : List (Nat × Nat × Nat) := [(2356572160,98615472758420,98615852286498),(2356645888,98615881842588,98616261370919)]
theorem point_links_checked17949 : (cuts17949.take 2).map (fun c => (2356543489-1+2*2^9*c.k,98615317243318+c.lower,98615696771302+c.upper)) = pointBounds17949 := by
 decide +kernel
def cuts17950 : List PrefixCut := [⟨44,251174288,251174440⟩,
⟨116,657844281,657844683⟩,
⟨128,723173028,723173473⟩]
theorem checked17950 : checkPrefixCuts (2^48) 2356674561 9 Manual.Count131072.C017950.packed 128 cuts17950 = true := by
 decide +kernel
def pointBounds17950 : List (Nat × Nat × Nat) := [(2356719616,98616292108358,98616671636937),(2356793344,98616698778351,98617078307180)]
theorem point_links_checked17950 : (cuts17950.take 2).map (fun c => (2356674561-1+2*2^9*c.k,98616040934070+c.lower,98616420462497+c.upper)) = pointBounds17950 := by
 decide +kernel
def cuts17951 : List PrefixCut := [⟨60,343119888,343120093⟩,
⟨128,731611966,731612403⟩]
theorem checked17951 : checkPrefixCuts (2^48) 2356805633 9 Manual.Count131072.C017951.packed 128 cuts17951 = true := by
 decide +kernel
def pointBounds17951 : List (Nat × Nat × Nat) := [(2356867072,98617107226986,98617486756063)]
theorem point_links_checked17951 : (cuts17951.take 1).map (fun c => (2356805633-1+2*2^9*c.k,98616764107098+c.lower,98617143635970+c.upper)) = pointBounds17951 := by
 decide +kernel
def cuts17952 : List PrefixCut := [⟨4,22332274,22332289⟩,
⟨76,427889281,427889550⟩,
⟨128,723689482,723689933⟩]
theorem checked17952 : checkPrefixCuts (2^48) 2356936705 9 Manual.Count131072.C017952.packed 128 cuts17952 = true := by
 decide +kernel
def pointBounds17952 : List (Nat × Nat × Nat) := [(2356940800,98617518051338,98617897580662),(2357014528,98617923608345,98618303137923)]
theorem point_links_checked17952 : (cuts17952.take 2).map (fun c => (2356936705-1+2*2^9*c.k,98617495719064+c.lower,98617875248373+c.upper)) = pointBounds17952 := by
 decide +kernel
def cuts17953 : List PrefixCut := [⟨20,107475183,107475246⟩,
⟨92,513842558,513842876⟩,
⟨128,716484192,716484633⟩]
theorem checked17953 : checkPrefixCuts (2^48) 2357067777 9 Manual.Count131072.C017953.packed 128 cuts17953 = true := by
 decide +kernel
def pointBounds17953 : List (Nat × Nat × Nat) := [(2357088256,98618326883729,98618706413552),(2357161984,98618733251104,98619112781182)]
theorem point_links_checked17953 : (cuts17953.take 2).map (fun c => (2357067777-1+2*2^9*c.k,98618219408546+c.lower,98618598938306+c.upper)) = pointBounds17953 := by
 decide +kernel
def cuts17954 : List PrefixCut := [⟨36,204668420,204668545⟩,
⟨108,611965804,611966182⟩,
⟨128,728743540,728743988⟩]
theorem checked17954 : checkPrefixCuts (2^48) 2357198849 9 Manual.Count131072.C017954.packed 128 cuts17954 = true := by
 decide +kernel
def pointBounds17954 : List (Nat × Nat × Nat) := [(2357235712,98619140561158,98619520091484),(2357309440,98619547858542,98619927389121)]
theorem point_links_checked17954 : (cuts17954.take 2).map (fun c => (2357198849-1+2*2^9*c.k,98618935892738+c.lower,98619315422939+c.upper)) = pointBounds17954 := by
 decide +kernel
def cuts17955 : List PrefixCut := [⟨52,293372610,293372786⟩,
⟨124,696465443,696465866⟩,
⟨128,719389779,719390217⟩]
theorem checked17955 : checkPrefixCuts (2^48) 2357329921 9 Manual.Count131072.C017955.packed 128 cuts17955 = true := by
 decide +kernel
def pointBounds17955 : List (Nat × Nat × Nat) := [(2357383168,98619958008888,98620337539713),(2357456896,98620361101721,98620740632793)]
theorem point_links_checked17955 : (cuts17955.take 2).map (fun c => (2357329921-1+2*2^9*c.k,98619664636278+c.lower,98620044166927+c.upper)) = pointBounds17955 := by
 decide +kernel
def cuts17956 : List PrefixCut := [⟨68,385528782,385529017⟩,
⟨128,722095954,722096399⟩]
theorem checked17956 : checkPrefixCuts (2^48) 2357460993 9 Manual.Count131072.C017956.packed 128 cuts17956 = true := by
 decide +kernel
def pointBounds17956 : List (Nat × Nat × Nat) := [(2357530624,98620769554839,98621149086161)]
theorem point_links_checked17956 : (cuts17956.take 1).map (fun c => (2357460993-1+2*2^9*c.k,98620384026057+c.lower,98620763557144+c.upper)) = pointBounds17956 := by
 decide +kernel
def cuts17957 : List PrefixCut := [⟨12,66858690,66858729⟩,
⟨84,479703586,479703874⟩,
⟨128,729099570,729100007⟩]
theorem checked17957 : checkPrefixCuts (2^48) 2357592065 9 Manual.Count131072.C017957.packed 128 cuts17957 = true := by
 decide +kernel
def pointBounds17957 : List (Nat × Nat × Nat) := [(2357604352,98621172980701,98621552512272),(2357678080,98621585825597,98621965357417)]
theorem point_links_checked17957 : (cuts17957.take 2).map (fun c => (2357592065-1+2*2^9*c.k,98621106122011+c.lower,98621485653543+c.upper)) = pointBounds17957 := by
 decide +kernel
def cuts17958 : List PrefixCut := [⟨28,160212617,160212712⟩,
⟨100,570524751,570525106⟩,
⟨128,730969181,730969634⟩]
theorem checked17958 : checkPrefixCuts (2^48) 2357723137 9 Manual.Count131072.C017958.packed 128 cuts17958 = true := by
 decide +kernel
def pointBounds17958 : List (Nat × Nat × Nat) := [(2357751808,98621995434198,98622374966262),(2357825536,98622405746332,98622785278656)]
theorem point_links_checked17958 : (cuts17958.take 2).map (fun c => (2357723137-1+2*2^9*c.k,98621835221581+c.lower,98622214753550+c.upper)) = pointBounds17958 := by
 decide +kernel
def cuts17959 : List PrefixCut := [⟨44,244482912,244483061⟩,
⟨116,656798676,656799081⟩,
⟨128,722691598,722692045⟩]
theorem checked17959 : checkPrefixCuts (2^48) 2357854209 9 Manual.Count131072.C017959.packed 128 cuts17959 = true := by
 decide +kernel
def pointBounds17959 : List (Nat × Nat × Nat) := [(2357899264,98622810673674,98623190206245),(2357972992,98623222989438,98623602522265)]
theorem point_links_checked17959 : (cuts17959.take 2).map (fun c => (2357854209-1+2*2^9*c.k,98622566190762+c.lower,98622945723184+c.upper)) = pointBounds17959 := by
 decide +kernel
def cuts17960 : List PrefixCut := [⟨60,342590130,342590337⟩,
⟨128,730768602,730769043⟩]
theorem checked17960 : checkPrefixCuts (2^48) 2357985281 9 Manual.Count131072.C017960.packed 128 cuts17960 = true := by
 decide +kernel
def pointBounds17960 : List (Nat × Nat × Nat) := [(2358046720,98623631472490,98624011005566)]
theorem point_links_checked17960 : (cuts17960.take 1).map (fun c => (2357985281-1+2*2^9*c.k,98623288882360+c.lower,98623668415229+c.upper)) = pointBounds17960 := by
 decide +kernel
def cuts17961 : List PrefixCut := [⟨4,21843647,21843661⟩,
⟨76,432807796,432808061⟩,
⟨128,725476082,725476523⟩]
theorem checked17961 : checkPrefixCuts (2^48) 2358116353 9 Manual.Count131072.C017961.packed 128 cuts17961 = true := by
 decide +kernel
def pointBounds17961 : List (Nat × Nat × Nat) := [(2358120448,98624041494609,98624421027933),(2358194176,98624452458758,98624831992333)]
theorem point_links_checked17961 : (cuts17961.take 2).map (fun c => (2358116353-1+2*2^9*c.k,98624019650962+c.lower,98624399184272+c.upper)) = pointBounds17961 := by
 decide +kernel
def cuts17962 : List PrefixCut := [⟨20,116731277,116731351⟩,
⟨92,529101931,529102261⟩,
⟨128,727822919,727823375⟩]
theorem checked17962 : checkPrefixCuts (2^48) 2358247425 9 Manual.Count131072.C017962.packed 128 cuts17962 = true := by
 decide +kernel
def pointBounds17962 : List (Nat × Nat × Nat) := [(2358267904,98624861858321,98625241392146),(2358341632,98625274228975,98625653763056)]
theorem point_links_checked17962 : (cuts17962.take 2).map (fun c => (2358247425-1+2*2^9*c.k,98624745127044+c.lower,98625124660795+c.upper)) = pointBounds17962 := by
 decide +kernel
def cuts17963 : List PrefixCut := [⟨36,203133860,203133987⟩,
⟨108,614285255,614285634⟩,
⟨128,729691797,729692248⟩]
theorem checked17963 : checkPrefixCuts (2^48) 2358378497 9 Manual.Count131072.C017963.packed 128 cuts17963 = true := by
 decide +kernel
def pointBounds17963 : List (Nat × Nat × Nat) := [(2358415360,98625676083823,98626055618157),(2358489088,98626087235218,98626466769804)]
theorem point_links_checked17963 : (cuts17963.take 2).map (fun c => (2358378497-1+2*2^9*c.k,98625472949963+c.lower,98625852484170+c.upper)) = pointBounds17963 := by
 decide +kernel
def cuts17964 : List PrefixCut := [⟨52,297522208,297522391⟩,
⟨124,705425844,705426279⟩,
⟨128,727742024,727742473⟩]
theorem checked17964 : checkPrefixCuts (2^48) 2358509569 9 Manual.Count131072.C017964.packed 128 cuts17964 = true := by
 decide +kernel
def pointBounds17964 : List (Nat × Nat × Nat) := [(2358562816,98626500163968,98626879698809),(2358636544,98626908067604,98627287602697)]
theorem point_links_checked17964 : (cuts17964.take 2).map (fun c => (2358509569-1+2*2^9*c.k,98626202641760+c.lower,98626582176418+c.upper)) = pointBounds17964 := by
 decide +kernel
def cuts17965 : List PrefixCut := [⟨68,379011093,379011320⟩,
⟨128,717677246,717677679⟩]
theorem checked17965 : checkPrefixCuts (2^48) 2358640641 9 Manual.Count131072.C017965.packed 128 cuts17965 = true := by
 decide +kernel
def pointBounds17965 : List (Nat × Nat × Nat) := [(2358710272,98627309394877,98627688930211)]
theorem point_links_checked17965 : (cuts17965.take 1).map (fun c => (2358640641-1+2*2^9*c.k,98626930383784+c.lower,98627309918891+c.upper)) = pointBounds17965 := by
 decide +kernel
def cuts17966 : List PrefixCut := [⟨12,71956485,71956529⟩,
⟨84,474929351,474929634⟩,
⟨128,725274555,725274992⟩]
theorem checked17966 : checkPrefixCuts (2^48) 2358771713 9 Manual.Count131072.C017966.packed 128 cuts17966 = true := by
 decide +kernel
def pointBounds17966 : List (Nat × Nat × Nat) := [(2358784000,98627720017515,98628099553099),(2358857728,98628122990381,98628502526204)]
theorem point_links_checked17966 : (cuts17966.take 2).map (fun c => (2358771713-1+2*2^9*c.k,98627648061030+c.lower,98628027596570+c.upper)) = pointBounds17966 := by
 decide +kernel
def cuts17967 : List PrefixCut := [⟨28,154882267,154882363⟩,
⟨100,563437957,563438303⟩,
⟨128,719506687,719507127⟩]
theorem checked17967 : checkPrefixCuts (2^48) 2358902785 9 Manual.Count131072.C017967.packed 128 cuts17967 = true := by
 decide +kernel
def pointBounds17967 : List (Nat × Nat × Nat) := [(2358931456,98628528217852,98628907753925),(2359005184,98628936773542,98629316309865)]
theorem point_links_checked17967 : (cuts17967.take 2).map (fun c => (2358902785-1+2*2^9*c.k,98628373335585+c.lower,98628752871562+c.upper)) = pointBounds17967 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000248
