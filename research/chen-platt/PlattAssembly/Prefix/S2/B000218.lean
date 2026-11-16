import PlattAssemblyKernel
import PlattCertificates.Count131072.C016976
import PlattCertificates.Count131072.C016977
import PlattCertificates.Count131072.C016978
import PlattCertificates.Count131072.C016979
import PlattCertificates.Count131072.C016980
import PlattCertificates.Count131072.C016981
import PlattCertificates.Count131072.C016982
import PlattCertificates.Count131072.C016983
import PlattCertificates.Count131072.C016984
import PlattCertificates.Count131072.C016985
import PlattCertificates.Count131072.C016986
import PlattCertificates.Count131072.C016987
import PlattCertificates.Count131072.C016988
import PlattCertificates.Count131072.C016989
import PlattCertificates.Count131072.C016990
import PlattCertificates.Count131072.C016991
import PlattCertificates.Count131072.C016992
import PlattCertificates.Count131072.C016993
import PlattCertificates.Count131072.C016994
import PlattCertificates.Count131072.C016995
import PlattCertificates.Count131072.C016996
import PlattCertificates.Count131072.C016997
import PlattCertificates.Count131072.C016998
import PlattCertificates.Count131072.C016999
import PlattCertificates.Count131072.C017000
import PlattCertificates.Count131072.C017001
import PlattCertificates.Count131072.C017002
import PlattCertificates.Count131072.C017003
import PlattCertificates.Count131072.C017004
import PlattCertificates.Count131072.C017005
import PlattCertificates.Count131072.C017006
import PlattCertificates.Count131072.C017007
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000218
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16976 : List PrefixCut := [⟨2,13132902,13132909⟩,
⟨71,434894254,434894524⟩,
⟨128,771662103,771662580⟩]
theorem checked16976 : checkPrefixCuts (2^48) 2229010433 9 Manual.Count131072.C016976.packed 128 cuts16976 = true := by
 decide +kernel
def pointBounds16976 : List (Nat × Nat × Nat) := [(2229012480,97888608026813,97888987105491),(2229083136,97889029788165,97889408867106)]
theorem point_links_checked16976 : (cuts16976.take 2).map (fun c => (2229010433-1+2*2^9*c.k,97888594893911+c.lower,97888973972582+c.upper)) = pointBounds16976 := by
 decide +kernel
def cuts16977 : List PrefixCut := [⟨12,73110441,73110486⟩,
⟨81,488026690,488026996⟩,
⟨128,773889446,773889928⟩]
theorem checked16977 : checkPrefixCuts (2^48) 2229141505 9 Manual.Count131072.C016977.packed 128 cuts16977 = true := by
 decide +kernel
def pointBounds16977 : List (Nat × Nat × Nat) := [(2229153792,97889439666455,97889818745648),(2229224448,97889854582704,97890233662158)]
theorem point_links_checked16977 : (cuts16977.take 2).map (fun c => (2229141505-1+2*2^9*c.k,97889366556014+c.lower,97889745635162+c.upper)) = pointBounds16977 := by
 decide +kernel
def cuts16978 : List PrefixCut := [⟨22,137626106,137626192⟩,
⟨91,564384386,564384740⟩,
⟨128,787858841,787859336⟩]
theorem checked16978 : checkPrefixCuts (2^48) 2229272577 9 Manual.Count131072.C016978.packed 128 cuts16978 = true := by
 decide +kernel
def pointBounds16978 : List (Nat × Nat × Nat) := [(2229295104,97890278071566,97890657151282),(2229365760,97890704829846,97891083909830)]
theorem point_links_checked16978 : (cuts16978.take 2).map (fun c => (2229272577-1+2*2^9*c.k,97890140445460+c.lower,97890519525090+c.upper)) = pointBounds16978 := by
 decide +kernel
def cuts16979 : List PrefixCut := [⟨32,190644694,190644811⟩,
⟨101,609422033,609422412⟩,
⟨128,772788275,772788759⟩]
theorem checked16979 : checkPrefixCuts (2^48) 2229403649 9 Manual.Count131072.C016979.packed 128 cuts16979 = true := by
 decide +kernel
def pointBounds16979 : List (Nat × Nat × Nat) := [(2229436416,97891118948995,97891498029237),(2229507072,97891537726334,97891916806838)]
theorem point_links_checked16979 : (cuts16979.take 2).map (fun c => (2229403649-1+2*2^9*c.k,97890928304301+c.lower,97891307384426+c.upper)) = pointBounds16979 := by
 decide +kernel
def cuts16980 : List PrefixCut := [⟨42,250726641,250726798⟩,
⟨111,664427602,664428011⟩,
⟨128,768071736,768072212⟩]
theorem checked16980 : checkPrefixCuts (2^48) 2229534721 9 Manual.Count131072.C016980.packed 128 cuts16980 = true := by
 decide +kernel
def pointBounds16980 : List (Nat × Nat × Nat) := [(2229577728,97891951819217,97892330899983),(2229648384,97892365520178,97892744601196)]
theorem point_links_checked16980 : (cuts16980.take 2).map (fun c => (2229534721-1+2*2^9*c.k,97891701092576+c.lower,97892080173185+c.upper)) = pointBounds16980 := by
 decide +kernel
def cuts16981 : List PrefixCut := [⟨52,310422555,310422749⟩,
⟨121,724854825,724855278⟩,
⟨128,768657897,768658379⟩]
theorem checked16981 : checkPrefixCuts (2^48) 2229665793 9 Manual.Count131072.C016981.packed 128 cuts16981 = true := by
 decide +kernel
def pointBounds16981 : List (Nat × Nat × Nat) := [(2229719040,97892779586867,97893158668146),(2229789696,97893194019137,97893573100675)]
theorem point_links_checked16981 : (cuts16981.take 2).map (fun c => (2229665793-1+2*2^9*c.k,97892469164312+c.lower,97892848245397+c.upper)) = pointBounds16981 := by
 decide +kernel
def cuts16982 : List PrefixCut := [⟨62,369984845,369985079⟩,
⟨128,762932423,762932901⟩]
theorem checked16982 : checkPrefixCuts (2^48) 2229796865 9 Manual.Count131072.C016982.packed 128 cuts16982 = true := by
 decide +kernel
def pointBounds16982 : List (Nat × Nat × Nat) := [(2229860352,97893607807054,97893986888855)]
theorem point_links_checked16982 : (cuts16982.take 1).map (fun c => (2229796865-1+2*2^9*c.k,97893237822209+c.lower,97893616903776+c.upper)) = pointBounds16982 := by
 decide +kernel
def cuts16983 : List PrefixCut := [⟨3,19060113,19060125⟩,
⟨72,436734807,436735078⟩,
⟨128,770839689,770840169⟩]
theorem checked16983 : checkPrefixCuts (2^48) 2229927937 9 Manual.Count131072.C016983.packed 128 cuts16983 = true := by
 decide +kernel
def pointBounds16983 : List (Nat × Nat × Nat) := [(2229931008,97894019814745,97894398896802),(2230001664,97894437489439,97894816571755)]
theorem point_links_checked16983 : (cuts16983.take 2).map (fun c => (2229927937-1+2*2^9*c.k,97894000754632+c.lower,97894379836677+c.upper)) = pointBounds16983 := by
 decide +kernel
def cuts16984 : List PrefixCut := [⟨13,77119326,77119374⟩,
⟨82,489718927,489719235⟩,
⟨128,762590350,762590826⟩]
theorem checked16984 : checkPrefixCuts (2^48) 2230059009 9 Manual.Count131072.C016984.packed 128 cuts16984 = true := by
 decide +kernel
def pointBounds16984 : List (Nat × Nat × Nat) := [(2230072320,97894848713647,97895227796220),(2230142976,97895261313248,97895640396081)]
theorem point_links_checked16984 : (cuts16984.take 2).map (fun c => (2230059009-1+2*2^9*c.k,97894771594321+c.lower,97895150676846+c.upper)) = pointBounds16984 := by
 decide +kernel
def cuts16985 : List PrefixCut := [⟨23,139967459,139967544⟩,
⟨92,554433957,554434307⟩,
⟨128,766079372,766079854⟩]
theorem checked16985 : checkPrefixCuts (2^48) 2230190081 9 Manual.Count131072.C016985.packed 128 cuts16985 = true := by
 decide +kernel
def pointBounds16985 : List (Nat × Nat × Nat) := [(2230213632,97895674152130,97896053235216),(2230284288,97896088618628,97896467701979)]
theorem point_links_checked16985 : (cuts16985.take 2).map (fun c => (2230190081-1+2*2^9*c.k,97895534184671+c.lower,97895913267672+c.upper)) = pointBounds16985 := by
 decide +kernel
def cuts16986 : List PrefixCut := [⟨33,198895596,198895720⟩,
⟨102,610054723,610055108⟩,
⟨128,767674895,767675377⟩]
theorem checked16986 : checkPrefixCuts (2^48) 2230321153 9 Manual.Count131072.C016986.packed 128 cuts16986 = true := by
 decide +kernel
def pointBounds16986 : List (Nat × Nat × Nat) := [(2230354944,97896499159639,97896878243246),(2230425600,97896910318766,97897289402634)]
theorem point_links_checked16986 : (cuts16986.take 2).map (fun c => (2230321153-1+2*2^9*c.k,97896300264043+c.lower,97896679347526+c.upper)) = pointBounds16986 := by
 decide +kernel
def cuts16987 : List PrefixCut := [⟨43,256049823,256049984⟩,
⟨112,671725838,671726256⟩,
⟨128,765484548,765485026⟩]
theorem checked16987 : checkPrefixCuts (2^48) 2230452225 9 Manual.Count131072.C016987.packed 128 cuts16987 = true := by
 decide +kernel
def pointBounds16987 : List (Nat × Nat × Nat) := [(2230496256,97897323988761,97897703072887),(2230566912,97897739664776,97898118749159)]
theorem point_links_checked16987 : (cuts16987.take 2).map (fun c => (2230452225-1+2*2^9*c.k,97897067938938+c.lower,97897447022903+c.upper)) = pointBounds16987 := by
 decide +kernel
def cuts16988 : List PrefixCut := [⟨53,321777839,321778037⟩,
⟨122,739951161,739951619⟩,
⟨128,776165302,776165784⟩]
theorem checked16988 : checkPrefixCuts (2^48) 2230583297 9 Manual.Count131072.C016988.packed 128 cuts16988 = true := by
 decide +kernel
def pointBounds16988 : List (Nat × Nat × Nat) := [(2230637568,97898155201325,97898534285966),(2230708224,97898573374647,97898952459548)]
theorem point_links_checked16988 : (cuts16988.take 2).map (fun c => (2230583297-1+2*2^9*c.k,97897833423486+c.lower,97898212507929+c.upper)) = pointBounds16988 := by
 decide +kernel
def cuts16989 : List PrefixCut := [⟨63,378665235,378665472⟩,
⟨128,770189244,770189725⟩]
theorem checked16989 : checkPrefixCuts (2^48) 2230714369 9 Manual.Count131072.C016989.packed 128 cuts16989 = true := by
 decide +kernel
def pointBounds16989 : List (Nat × Nat × Nat) := [(2230778880,97898988254023,97899367339185)]
theorem point_links_checked16989 : (cuts16989.take 1).map (fun c => (2230714369-1+2*2^9*c.k,97898609588788+c.lower,97898988673713+c.upper)) = pointBounds16989 := by
 decide +kernel
def cuts16990 : List PrefixCut := [⟨4,24351577,24351592⟩,
⟨73,441475649,441475924⟩,
⟨128,774181383,774181864⟩]
theorem checked16990 : checkPrefixCuts (2^48) 2230845441 9 Manual.Count131072.C016990.packed 128 cuts16990 = true := by
 decide +kernel
def pointBounds16990 : List (Nat × Nat × Nat) := [(2230849536,97899404129609,97899783215030),(2230920192,97899821253681,97900200339362)]
theorem point_links_checked16990 : (cuts16990.take 2).map (fun c => (2230845441-1+2*2^9*c.k,97899379778032+c.lower,97899758863438+c.upper)) = pointBounds16990 := by
 decide +kernel
def cuts16991 : List PrefixCut := [⟨14,84531402,84531453⟩,
⟨83,497970302,497970613⟩,
⟨128,766566122,766566602⟩]
theorem checked16991 : checkPrefixCuts (2^48) 2230976513 9 Manual.Count131072.C016991.packed 128 cuts16991 = true := by
 decide +kernel
def pointBounds16991 : List (Nat × Nat × Nat) := [(2230990848,97900238490817,97900617576755),(2231061504,97900651929717,97901031015915)]
theorem point_links_checked16991 : (cuts16991.take 2).map (fun c => (2230976513-1+2*2^9*c.k,97900153959415+c.lower,97900533045302+c.upper)) = pointBounds16991 := by
 decide +kernel
def cuts16992 : List PrefixCut := [⟨24,141802234,141802322⟩,
⟨93,561144395,561144742⟩,
⟨128,770053506,770053982⟩]
theorem checked16992 : checkPrefixCuts (2^48) 2231107585 9 Manual.Count131072.C016992.packed 128 cuts16992 = true := by
 decide +kernel
def pointBounds16992 : List (Nat × Nat × Nat) := [(2231132160,97901062327771,97901441414226),(2231202816,97901481669932,97901860756646)]
theorem point_links_checked16992 : (cuts16992.take 2).map (fun c => (2231107585-1+2*2^9*c.k,97900920525537+c.lower,97901299611904+c.upper)) = pointBounds16992 := by
 decide +kernel
def cuts16993 : List PrefixCut := [⟨34,198435316,198435442⟩,
⟨103,613335759,613336139⟩,
⟨128,758907292,758907765⟩]
theorem checked16993 : checkPrefixCuts (2^48) 2231238657 9 Manual.Count131072.C016993.packed 128 cuts16993 = true := by
 decide +kernel
def pointBounds16993 : List (Nat × Nat × Nat) := [(2231273472,97901889014359,97902268101328),(2231344128,97902303914802,97902683002025)]
theorem point_links_checked16993 : (cuts16993.take 2).map (fun c => (2231238657-1+2*2^9*c.k,97901690579043+c.lower,97902069665886+c.upper)) = pointBounds16993 := by
 decide +kernel
def cuts16994 : List PrefixCut := [⟨44,263008539,263008702⟩,
⟨113,676747431,676747847⟩,
⟨128,766683445,766683917⟩]
theorem checked16994 : checkPrefixCuts (2^48) 2231369729 9 Manual.Count131072.C016994.packed 128 cuts16994 = true := by
 decide +kernel
def pointBounds16994 : List (Nat × Nat × Nat) := [(2231414784,97902712494874,97903091582353),(2231485440,97903126233766,97903505321498)]
theorem point_links_checked16994 : (cuts16994.take 2).map (fun c => (2231369729-1+2*2^9*c.k,97902449486335+c.lower,97902828573651+c.upper)) = pointBounds16994 := by
 decide +kernel
def cuts16995 : List PrefixCut := [⟨54,327447683,327447889⟩,
⟨123,743304610,743305074⟩,
⟨128,772692848,772693330⟩]
theorem checked16995 : checkPrefixCuts (2^48) 2231500801 9 Manual.Count131072.C016995.packed 128 cuts16995 = true := by
 decide +kernel
def pointBounds16995 : List (Nat × Nat × Nat) := [(2231556096,97903543617463,97903922705457),(2231626752,97903959474390,97904338562642)]
theorem point_links_checked16995 : (cuts16995.take 2).map (fun c => (2231500801-1+2*2^9*c.k,97903216169780+c.lower,97903595257568+c.upper)) = pointBounds16995 := by
 decide +kernel
def cuts16996 : List PrefixCut := [⟨64,381536521,381536756⟩,
⟨128,766845561,766846040⟩]
theorem checked16996 : checkPrefixCuts (2^48) 2231631873 9 Manual.Count131072.C016996.packed 128 cuts16996 = true := by
 decide +kernel
def pointBounds16996 : List (Nat × Nat × Nat) := [(2231697408,97904370399149,97904749487654)]
theorem point_links_checked16996 : (cuts16996.take 1).map (fun c => (2231631873-1+2*2^9*c.k,97903988862628+c.lower,97904367950898+c.upper)) = pointBounds16996 := by
 decide +kernel
def cuts16997 : List PrefixCut := [⟨5,31656639,31656659⟩,
⟨74,446212870,446213151⟩,
⟨128,768187931,768188410⟩]
theorem checked16997 : checkPrefixCuts (2^48) 2231762945 9 Manual.Count131072.C016997.packed 128 cuts16997 = true := by
 decide +kernel
def pointBounds16997 : List (Nat × Nat × Nat) := [(2231768064,97904787364828,97905166453597),(2231838720,97905201921059,97905581010089)]
theorem point_links_checked16997 : (cuts16997.take 2).map (fun c => (2231762945-1+2*2^9*c.k,97904755708189+c.lower,97905134796938+c.upper)) = pointBounds16997 := by
 decide +kernel
def cuts16998 : List PrefixCut := [⟨15,91432933,91432991⟩,
⟨84,505836783,505837097⟩,
⟨128,765999030,765999506⟩]
theorem checked16998 : checkPrefixCuts (2^48) 2231894017 9 Manual.Count131072.C016998.packed 128 cuts16998 = true := by
 decide +kernel
def pointBounds16998 : List (Nat × Nat × Nat) := [(2231909376,97905615329053,97905994418339),(2231980032,97906029732903,97906408822445)]
theorem point_links_checked16998 : (cuts16998.take 2).map (fun c => (2231894017-1+2*2^9*c.k,97905523896120+c.lower,97905902985348+c.upper)) = pointBounds16998 := by
 decide +kernel
def cuts16999 : List PrefixCut := [⟨25,148427562,148427652⟩,
⟨94,562552983,562553330⟩,
⟨128,768097626,768098103⟩]
theorem checked16999 : checkPrefixCuts (2^48) 2232025089 9 Manual.Count131072.C016999.packed 128 cuts16999 = true := by
 decide +kernel
def pointBounds16999 : List (Nat × Nat × Nat) := [(2232050688,97906438322712,97906817412506),(2232121344,97906852448133,97907231538184)]
theorem point_links_checked16999 : (cuts16999.take 2).map (fun c => (2232025089-1+2*2^9*c.k,97906289895150+c.lower,97906668984854+c.upper)) = pointBounds16999 := by
 decide +kernel
def cuts17000 : List PrefixCut := [⟨35,209828729,209828860⟩,
⟨104,617623075,617623462⟩,
⟨128,759351922,759352399⟩]
theorem checked17000 : checkPrefixCuts (2^48) 2232156161 9 Manual.Count131072.C017000.packed 128 cuts17000 = true := by
 decide +kernel
def pointBounds17000 : List (Nat × Nat × Nat) := [(2232192000,97907267821505,97907646911817),(2232262656,97907675615851,97908054706419)]
theorem point_links_checked17000 : (cuts17000.take 2).map (fun c => (2232156161-1+2*2^9*c.k,97907057992776+c.lower,97907437082957+c.upper)) = pointBounds17000 := by
 decide +kernel
def cuts17001 : List PrefixCut := [⟨45,272105069,272105237⟩,
⟨114,685799766,685800192⟩,
⟨128,767377148,767377623⟩]
theorem checked17001 : checkPrefixCuts (2^48) 2232287233 9 Manual.Count131072.C017001.packed 128 cuts17001 = true := by
 decide +kernel
def pointBounds17001 : List (Nat × Nat × Nat) := [(2232333312,97908089449767,97908468540593),(2232403968,97908503144464,97908882235548)]
theorem point_links_checked17001 : (cuts17001.take 2).map (fun c => (2232287233-1+2*2^9*c.k,97907817344698+c.lower,97908196435356+c.upper)) = pointBounds17001 := by
 decide +kernel
def cuts17002 : List PrefixCut := [⟨55,328952099,328952307⟩,
⟨124,741738107,741738572⟩,
⟨128,764558207,764558687⟩]
theorem checked17002 : checkPrefixCuts (2^48) 2232418305 9 Manual.Count131072.C017002.packed 128 cuts17002 = true := by
 decide +kernel
def pointBounds17002 : List (Nat × Nat × Nat) := [(2232474624,97908913673945,97909292765286),(2232545280,97909326459953,97909705551551)]
theorem point_links_checked17002 : (cuts17002.take 2).map (fun c => (2232418305-1+2*2^9*c.k,97908584721846+c.lower,97908963812979+c.upper)) = pointBounds17002 := by
 decide +kernel
def cuts17003 : List PrefixCut := [⟨65,382009999,382010237⟩,
⟨128,760478722,760479192⟩]
theorem checked17003 : checkPrefixCuts (2^48) 2232549377 9 Manual.Count131072.C017003.packed 128 cuts17003 = true := by
 decide +kernel
def pointBounds17003 : List (Nat × Nat × Nat) := [(2232615936,97909731290052,97910110381903)]
theorem point_links_checked17003 : (cuts17003.take 1).map (fun c => (2232549377-1+2*2^9*c.k,97909349280053+c.lower,97909728371666+c.upper)) = pointBounds17003 := by
 decide +kernel
def cuts17004 : List PrefixCut := [⟨6,33660746,33660768⟩,
⟨75,447163975,447164256⟩,
⟨128,758165099,758165574⟩]
theorem checked17004 : checkPrefixCuts (2^48) 2232680449 9 Manual.Count131072.C017004.packed 128 cuts17004 = true := by
 decide +kernel
def pointBounds17004 : List (Nat × Nat × Nat) := [(2232686592,97910143419521,97910522511626),(2232757248,97910556922750,97910936015114)]
theorem point_links_checked17004 : (cuts17004.take 2).map (fun c => (2232680449-1+2*2^9*c.k,97910109758775+c.lower,97910488850858+c.upper)) = pointBounds17004 := by
 decide +kernel
def cuts17005 : List PrefixCut := [⟨16,96059648,96059705⟩,
⟨85,514200964,514201277⟩,
⟨128,778794220,778794699⟩]
theorem checked17005 : checkPrefixCuts (2^48) 2232811521 9 Manual.Count131072.C017005.packed 128 cuts17005 = true := by
 decide +kernel
def pointBounds17005 : List (Nat × Nat × Nat) := [(2232827904,97910963983522,97911343076137),(2232898560,97911382124838,97911761217709)]
theorem point_links_checked17005 : (cuts17005.take 2).map (fun c => (2232811521-1+2*2^9*c.k,97910867923874+c.lower,97911247016432+c.upper)) = pointBounds17005 := by
 decide +kernel
def cuts17006 : List PrefixCut := [⟨26,156307977,156308075⟩,
⟨95,573288285,573288634⟩,
⟨128,773076173,773076651⟩]
theorem checked17006 : checkPrefixCuts (2^48) 2232942593 9 Manual.Count131072.C017006.packed 128 cuts17006 = true := by
 decide +kernel
def pointBounds17006 : List (Nat × Nat × Nat) := [(2232969216,97911803026071,97912182119206),(2233039872,97912220006379,97912599099765)]
theorem point_links_checked17006 : (cuts17006.take 2).map (fun c => (2232942593-1+2*2^9*c.k,97911646718094+c.lower,97912025811131+c.upper)) = pointBounds17006 := by
 decide +kernel
def cuts17007 : List PrefixCut := [⟨36,215792744,215792877⟩,
⟨105,625436069,625436453⟩,
⟨128,759796253,759796721⟩]
theorem checked17007 : checkPrefixCuts (2^48) 2233073665 9 Manual.Count131072.C017007.packed 128 cuts17007 = true := by
 decide +kernel
def pointBounds17007 : List (Nat × Nat × Nat) := [(2233110528,97912635587011,97913014680659),(2233181184,97913045230336,97913424324235)]
theorem point_links_checked17007 : (cuts17007.take 2).map (fun c => (2233073665-1+2*2^9*c.k,97912419794267+c.lower,97912798887782+c.upper)) = pointBounds17007 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000218
