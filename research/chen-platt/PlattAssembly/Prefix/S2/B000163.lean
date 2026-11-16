import PlattAssemblyKernel
import PlattCertificates.Count131072.C015216
import PlattCertificates.Count131072.C015217
import PlattCertificates.Count131072.C015218
import PlattCertificates.Count131072.C015219
import PlattCertificates.Count131072.C015220
import PlattCertificates.Count131072.C015221
import PlattCertificates.Count131072.C015222
import PlattCertificates.Count131072.C015223
import PlattCertificates.Count131072.C015224
import PlattCertificates.Count131072.C015225
import PlattCertificates.Count131072.C015226
import PlattCertificates.Count131072.C015227
import PlattCertificates.Count131072.C015228
import PlattCertificates.Count131072.C015229
import PlattCertificates.Count131072.C015230
import PlattCertificates.Count131072.C015231
import PlattCertificates.Count131072.C015232
import PlattCertificates.Count131072.C015233
import PlattCertificates.Count131072.C015234
import PlattCertificates.Count131072.C015235
import PlattCertificates.Count131072.C015236
import PlattCertificates.Count131072.C015237
import PlattCertificates.Count131072.C015238
import PlattCertificates.Count131072.C015239
import PlattCertificates.Count131072.C015240
import PlattCertificates.Count131072.C015241
import PlattCertificates.Count131072.C015242
import PlattCertificates.Count131072.C015243
import PlattCertificates.Count131072.C015244
import PlattCertificates.Count131072.C015245
import PlattCertificates.Count131072.C015246
import PlattCertificates.Count131072.C015247
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000163
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15216 : List PrefixCut := [⟨5,32255867,32255890⟩,
⟨66,441997098,441997393⟩,
⟨127,855105812,855106382⟩,
⟨128,861021356,861021930⟩]
theorem checked15216 : checkPrefixCuts (2^48) 1998323713 9 Manual.Count131072.C015216.packed 128 cuts15216 = true := by
 decide +kernel
def pointBounds15216 : List (Nat × Nat × Nat) := [(1998328832,96456428528238,96456806686679),(1998391296,96456838269469,96457216428182),(1998453760,96457251378183,96457629537171)]
theorem point_links_checked15216 : (cuts15216.take 3).map (fun c => (1998323713-1+2*2^9*c.k,96456396272371+c.lower,96456774430789+c.upper)) = pointBounds15216 := by
 decide +kernel
def cuts15217 : List PrefixCut := [⟨60,399433825,399434094⟩,
⟨121,802235481,802236021⟩,
⟨128,850260991,850261563⟩]
theorem checked15217 : checkPrefixCuts (2^48) 1998454785 9 Manual.Count131072.C015217.packed 128 cuts15217 = true := by
 decide +kernel
def pointBounds15217 : List (Nat × Nat × Nat) := [(1998516224,96457656727552,96458034886813),(1998578688,96458059529208,96458437688740)]
theorem point_links_checked15217 : (cuts15217.take 2).map (fun c => (1998454785-1+2*2^9*c.k,96457257293727+c.lower,96457635452719+c.upper)) = pointBounds15217 := by
 decide +kernel
def cuts15218 : List PrefixCut := [⟨54,363777012,363777252⟩,
⟨115,770637611,770638122⟩,
⟨128,862598466,862599037⟩]
theorem checked15218 : checkPrefixCuts (2^48) 1998585857 9 Manual.Count131072.C015218.packed 128 cuts15218 = true := by
 decide +kernel
def pointBounds15218 : List (Nat × Nat × Nat) := [(1998641152,96458471331730,96458849491534),(1998703616,96458878192329,96459256352404)]
theorem point_links_checked15218 : (cuts15218.take 2).map (fun c => (1998585857-1+2*2^9*c.k,96458107554718+c.lower,96458485714282+c.upper)) = pointBounds15218 := by
 decide +kernel
def cuts15219 : List PrefixCut := [⟨48,324604037,324604248⟩,
⟨109,736790262,736790746⟩,
⟨128,863105135,863105706⟩]
theorem checked15219 : checkPrefixCuts (2^48) 1998716929 9 Manual.Count131072.C015219.packed 128 cuts15219 = true := by
 decide +kernel
def pointBounds15219 : List (Nat × Nat × Nat) := [(1998766080,96459294757221,96459672917567),(1998828544,96459706943446,96460085104065)]
theorem point_links_checked15219 : (cuts15219.take 2).map (fun c => (1998716929-1+2*2^9*c.k,96458970153184+c.lower,96459348313319+c.upper)) = pointBounds15219 := by
 decide +kernel
def cuts15220 : List PrefixCut := [⟨42,284168807,284168998⟩,
⟨104,696470263,696470730⟩,
⟨128,856289816,856290388⟩]
theorem checked15220 : checkPrefixCuts (2^48) 1998848001 9 Manual.Count131072.C015220.packed 128 cuts15220 = true := by
 decide +kernel
def pointBounds15220 : List (Nat × Nat × Nat) := [(1998891008,96460117427126,96460495588023),(1998954496,96460529728582,96460907889755)]
theorem point_links_checked15220 : (cuts15220.take 2).map (fun c => (1998848001-1+2*2^9*c.k,96459833258319+c.lower,96460211419025+c.upper)) = pointBounds15220 := by
 decide +kernel
def cuts15221 : List PrefixCut := [⟨38,247540363,247540530⟩,
⟨100,665166029,665166467⟩,
⟨128,855529122,855529688⟩]
theorem checked15221 : checkPrefixCuts (2^48) 1998979073 9 Manual.Count131072.C015221.packed 128 cuts15221 = true := by
 decide +kernel
def pointBounds15221 : List (Nat × Nat × Nat) := [(1999017984,96460937088498,96461315249943),(1999081472,96461354714164,96461732875880)]
theorem point_links_checked15221 : (cuts15221.take 2).map (fun c => (1998979073-1+2*2^9*c.k,96460689548135+c.lower,96461067709413+c.upper)) = pointBounds15221 := by
 decide +kernel
def cuts15222 : List PrefixCut := [⟨34,221476623,221476773⟩,
⟨96,641750874,641751299⟩,
⟨128,856881076,856881645⟩]
theorem checked15222 : checkPrefixCuts (2^48) 1999110145 9 Manual.Count131072.C015222.packed 128 cuts15222 = true := by
 decide +kernel
def pointBounds15222 : List (Nat × Nat × Nat) := [(1999144960,96461766553880,96462144715874),(1999208448,96462186828131,96462564990400)]
theorem point_links_checked15222 : (cuts15222.take 2).map (fun c => (1999110145-1+2*2^9*c.k,96461545077257+c.lower,96461923239101+c.upper)) = pointBounds15222 := by
 decide +kernel
def cuts15223 : List PrefixCut := [⟨30,195838559,195838695⟩,
⟨92,624392543,624392961⟩,
⟨128,868369353,868369931⟩]
theorem checked15223 : checkPrefixCuts (2^48) 1999241217 9 Manual.Count131072.C015223.packed 128 cuts15223 = true := by
 decide +kernel
def pointBounds15223 : List (Nat × Nat × Nat) := [(1999271936,96462597796892,96462975959441),(1999335424,96463026350876,96463404513707)]
theorem point_links_checked15223 : (cuts15223.take 2).map (fun c => (1999241217-1+2*2^9*c.k,96462401958333+c.lower,96462780120746+c.upper)) = pointBounds15223 := by
 decide +kernel
def cuts15224 : List PrefixCut := [⟨26,174004942,174005057⟩,
⟨88,591128791,591129180⟩,
⟨128,860569949,860570517⟩]
theorem checked15224 : checkPrefixCuts (2^48) 1999372289 9 Manual.Count131072.C015224.packed 128 cuts15224 = true := by
 decide +kernel
def pointBounds15224 : List (Nat × Nat × Nat) := [(1999398912,96463444332628,96463822495734),(1999462400,96463861456477,96464239619857)]
theorem point_links_checked15224 : (cuts15224.take 2).map (fun c => (1999372289-1+2*2^9*c.k,96463270327686+c.lower,96463648490677+c.upper)) = pointBounds15224 := by
 decide +kernel
def cuts15225 : List PrefixCut := [⟨22,145698605,145698699⟩,
⟨84,564485147,564485514⟩,
⟨128,859387254,859387815⟩]
theorem checked15225 : checkPrefixCuts (2^48) 1999503361 9 Manual.Count131072.C015225.packed 128 cuts15225 = true := by
 decide +kernel
def pointBounds15225 : List (Nat × Nat × Nat) := [(1999525888,96464276596240,96464654759893),(1999589376,96464695382782,96465073546708)]
theorem point_links_checked15225 : (cuts15225.take 2).map (fun c => (1999503361-1+2*2^9*c.k,96464130897635+c.lower,96464509061194+c.upper)) = pointBounds15225 := by
 decide +kernel
def cuts15226 : List PrefixCut := [⟨18,122744928,122745009⟩,
⟨80,535311356,535311711⟩,
⟨128,852715372,852715936⟩]
theorem checked15226 : checkPrefixCuts (2^48) 1999634433 9 Manual.Count131072.C015226.packed 128 cuts15226 = true := by
 decide +kernel
def pointBounds15226 : List (Nat × Nat × Nat) := [(1999652864,96465113029817,96465491194018),(1999716352,96465525596245,96465903760720)]
theorem point_links_checked15226 : (cuts15226.take 2).map (fun c => (1999634433-1+2*2^9*c.k,96464990284889+c.lower,96465368449009+c.upper)) = pointBounds15226 := by
 decide +kernel
def cuts15227 : List PrefixCut := [⟨14,95993850,95993910⟩,
⟨76,519512821,519513165⟩,
⟨128,866734727,866735298⟩]
theorem checked15227 : checkPrefixCuts (2^48) 1999765505 9 Manual.Count131072.C015227.packed 128 cuts15227 = true := by
 decide +kernel
def pointBounds15227 : List (Nat × Nat × Nat) := [(1999779840,96465938994111,96466317158855),(1999843328,96466362513082,96466740678110)]
theorem point_links_checked15227 : (cuts15227.take 2).map (fun c => (1999765505-1+2*2^9*c.k,96465843000261+c.lower,96466221164945+c.upper)) = pointBounds15227 := by
 decide +kernel
def cuts15228 : List PrefixCut := [⟨10,70090689,70090737⟩,
⟨72,477115873,477116186⟩,
⟨128,851759136,851759695⟩]
theorem checked15228 : checkPrefixCuts (2^48) 1999896577 9 Manual.Count131072.C015228.packed 128 cuts15228 = true := by
 decide +kernel
def pointBounds15228 : List (Nat × Nat × Nat) := [(1999906816,96466779825677,96467157990980),(1999970304,96467186850861,96467565016429)]
theorem point_links_checked15228 : (cuts15228.take 2).map (fun c => (1999896577-1+2*2^9*c.k,96466709734988+c.lower,96467087900243+c.upper)) = pointBounds15228 := by
 decide +kernel
def cuts15229 : List PrefixCut := [⟨6,40391024,40391051⟩,
⟨68,465263584,465263890⟩,
⟨128,874361106,874361678⟩]
theorem checked15229 : checkPrefixCuts (2^48) 2000027649 9 Manual.Count131072.C015229.packed 128 cuts15229 = true := by
 decide +kernel
def pointBounds15229 : List (Nat × Nat × Nat) := [(2000033792,96467601885148,96467980050989),(2000097280,96468026757708,96468404923828)]
theorem point_links_checked15229 : (cuts15229.take 2).map (fun c => (2000027649-1+2*2^9*c.k,96467561494124+c.lower,96467939659938+c.upper)) = pointBounds15229 := by
 decide +kernel
def cuts15230 : List PrefixCut := [⟨2,12806084,12806093⟩,
⟨64,430333952,430334235⟩,
⟨126,843345469,843346023⟩,
⟨128,857135747,857136311⟩]
theorem checked15230 : checkPrefixCuts (2^48) 2000158721 9 Manual.Count131072.C015230.packed 128 cuts15230 = true := by
 decide +kernel
def pointBounds15230 : List (Nat × Nat × Nat) := [(2000160768,96468448661314,96468826827709),(2000224256,96468866189182,96469244355851),(2000287744,96469279200699,96469657367639)]
theorem point_links_checked15230 : (cuts15230.take 3).map (fun c => (2000158721-1+2*2^9*c.k,96468435855230+c.lower,96468814021616+c.upper)) = pointBounds15230 := by
 decide +kernel
def cuts15231 : List PrefixCut := [⟨60,404555261,404555533⟩,
⟨122,831330206,831330758⟩,
⟨128,870306332,870306912⟩]
theorem checked15231 : checkPrefixCuts (2^48) 2000289793 9 Manual.Count131072.C015231.packed 128 cuts15231 = true := by
 decide +kernel
def pointBounds15231 : List (Nat × Nat × Nat) := [(2000351232,96469697546238,96470075713460),(2000414720,96470124321183,96470502488685)]
theorem point_links_checked15231 : (cuts15231.take 2).map (fun c => (2000289793-1+2*2^9*c.k,96469292990977+c.lower,96469671157927+c.upper)) = pointBounds15231 := by
 decide +kernel
def cuts15232 : List PrefixCut := [⟨56,376247373,376247622⟩,
⟨118,788643642,788644168⟩,
⟨128,856460542,856461111⟩]
theorem checked15232 : checkPrefixCuts (2^48) 2000420865 9 Manual.Count131072.C015232.packed 128 cuts15232 = true := by
 decide +kernel
def pointBounds15232 : List (Nat × Nat × Nat) := [(2000478208,96470539544682,96470917712461),(2000541696,96470951940951,96471330109007)]
theorem point_links_checked15232 : (cuts15232.take 2).map (fun c => (2000420865-1+2*2^9*c.k,96470163297309+c.lower,96470541464839+c.upper)) = pointBounds15232 := by
 decide +kernel
def cuts15233 : List PrefixCut := [⟨52,350616325,350616558⟩,
⟨114,766503731,766504234⟩,
⟨128,860906656,860907222⟩]
theorem checked15233 : checkPrefixCuts (2^48) 2000551937 9 Manual.Count131072.C015233.packed 128 cuts15233 = true := by
 decide +kernel
def pointBounds15233 : List (Nat × Nat × Nat) := [(2000605184,96471370374176,96471748542508),(2000668672,96471786261582,96472164430184)]
theorem point_links_checked15233 : (cuts15233.take 2).map (fun c => (2000551937-1+2*2^9*c.k,96471019757851+c.lower,96471397925950+c.upper)) = pointBounds15233 := by
 decide +kernel
def cuts15234 : List PrefixCut := [⟨48,322034074,322034286⟩,
⟨110,738317180,738317668⟩,
⟨128,863101094,863101661⟩]
theorem checked15234 : checkPrefixCuts (2^48) 2000683009 9 Manual.Count131072.C015234.packed 128 cuts15234 = true := by
 decide +kernel
def pointBounds15234 : List (Nat × Nat × Nat) := [(2000732160,96472202698581,96472580867458),(2000795648,96472618981687,96472997150840)]
theorem point_links_checked15234 : (cuts15234.take 2).map (fun c => (2000683009-1+2*2^9*c.k,96471880664507+c.lower,96472258833172+c.upper)) = pointBounds15234 := by
 decide +kernel
def cuts15235 : List PrefixCut := [⟨44,296550538,296550732⟩,
⟨106,717871555,717872028⟩,
⟨128,867968319,867968888⟩]
theorem checked15235 : checkPrefixCuts (2^48) 2000814081 9 Manual.Count131072.C015235.packed 128 cuts15235 = true := by
 decide +kernel
def pointBounds15235 : List (Nat × Nat × Nat) := [(2000859136,96473040316139,96473418485565),(2000922624,96473461637156,96473839806861)]
theorem point_links_checked15235 : (cuts15235.take 2).map (fun c => (2000814081-1+2*2^9*c.k,96472743765601+c.lower,96473121934833+c.upper)) = pointBounds15235 := by
 decide +kernel
def cuts15236 : List PrefixCut := [⟨40,268678814,268678993⟩,
⟨102,692364377,692364831⟩,
⟨128,868896031,868896602⟩]
theorem checked15236 : checkPrefixCuts (2^48) 2000945153 9 Manual.Count131072.C015236.packed 128 cuts15236 = true := by
 decide +kernel
def pointBounds15236 : List (Nat × Nat × Nat) := [(2000986112,96473880412734,96474258582714),(2001049600,96474304098297,96474682268552)]
theorem point_links_checked15236 : (cuts15236.take 2).map (fun c => (2000945153-1+2*2^9*c.k,96473611733920+c.lower,96473989903721+c.upper)) = pointBounds15236 := by
 decide +kernel
def cuts15237 : List PrefixCut := [⟨36,244889819,244889978⟩,
⟨98,661796946,661797381⟩,
⟨128,862931583,862932152⟩]
theorem checked15237 : checkPrefixCuts (2^48) 2001076225 9 Manual.Count131072.C015237.packed 128 cuts15237 = true := by
 decide +kernel
def pointBounds15237 : List (Nat × Nat × Nat) := [(2001113088,96474725519770,96475103690301),(2001176576,96475142426897,96475520597704)]
theorem point_links_checked15237 : (cuts15237.take 2).map (fun c => (2001076225-1+2*2^9*c.k,96474480629951+c.lower,96474858800323+c.upper)) = pointBounds15237 := by
 decide +kernel
def cuts15238 : List PrefixCut := [⟨32,216181160,216181301⟩,
⟨94,631655405,631655820⟩,
⟨128,865969206,865969775⟩]
theorem checked15238 : checkPrefixCuts (2^48) 2001207297 9 Manual.Count131072.C015238.packed 128 cuts15238 = true := by
 decide +kernel
def pointBounds15238 : List (Nat × Nat × Nat) := [(2001240064,96475559742694,96475937913776),(2001303552,96475975216939,96476353388295)]
theorem point_links_checked15238 : (cuts15238.take 2).map (fun c => (2001207297-1+2*2^9*c.k,96475343561534+c.lower,96475721732475+c.upper)) = pointBounds15238 := by
 decide +kernel
def cuts15239 : List PrefixCut := [⟨28,194367671,194367801⟩,
⟨90,605596256,605596661⟩,
⟨128,855646140,855646710⟩]
theorem checked15239 : checkPrefixCuts (2^48) 2001338369 9 Manual.Count131072.C015239.packed 128 cuts15239 = true := by
 decide +kernel
def pointBounds15239 : List (Nat × Nat × Nat) := [(2001367040,96476403898411,96476782070051),(2001430528,96476815126996,96477193298911)]
theorem point_links_checked15239 : (cuts15239.take 2).map (fun c => (2001338369-1+2*2^9*c.k,96476209530740+c.lower,96476587702250+c.upper)) = pointBounds15239 := by
 decide +kernel
def cuts15240 : List PrefixCut := [⟨24,158071780,158071884⟩,
⟨86,579118463,579118846⟩,
⟨128,863324432,863324997⟩]
theorem checked15240 : checkPrefixCuts (2^48) 2001469441 9 Manual.Count131072.C015240.packed 128 cuts15240 = true := by
 decide +kernel
def pointBounds15240 : List (Nat × Nat × Nat) := [(2001494016,96477223248660,96477601420844),(2001557504,96477644295343,96478022467806)]
theorem point_links_checked15240 : (cuts15240.take 2).map (fun c => (2001469441-1+2*2^9*c.k,96477065176880+c.lower,96477443348960+c.upper)) = pointBounds15240 := by
 decide +kernel
def cuts15241 : List PrefixCut := [⟨20,137671074,137671165⟩,
⟨82,555597353,555597720⟩,
⟨128,865658631,865659199⟩]
theorem checked15241 : checkPrefixCuts (2^48) 2001600513 9 Manual.Count131072.C015241.packed 128 cuts15241 = true := by
 decide +kernel
def pointBounds15241 : List (Nat × Nat × Nat) := [(2001620992,96478066172386,96478444345122),(2001684480,96478484098665,96478862271677)]
theorem point_links_checked15241 : (cuts15241.take 2).map (fun c => (2001600513-1+2*2^9*c.k,96477928501312+c.lower,96478306673957+c.upper)) = pointBounds15241 := by
 decide +kernel
def cuts15242 : List PrefixCut := [⟨16,111226553,111226627⟩,
⟨78,531094984,531095335⟩,
⟨128,870664010,870664589⟩]
theorem checked15242 : checkPrefixCuts (2^48) 2001731585 9 Manual.Count131072.C015242.packed 128 cuts15242 = true := by
 decide +kernel
def pointBounds15242 : List (Nat × Nat × Nat) := [(2001747968,96478905386496,96479283559783),(2001811456,96479325254927,96479703428491)]
theorem point_links_checked15242 : (cuts15242.take 2).map (fun c => (2001731585-1+2*2^9*c.k,96478794159943+c.lower,96479172333156+c.upper)) = pointBounds15242 := by
 decide +kernel
def cuts15243 : List PrefixCut := [⟨12,77755140,77755193⟩,
⟨74,498440469,498440799⟩,
⟨128,866810448,866811014⟩]
theorem checked15243 : checkPrefixCuts (2^48) 2001862657 9 Manual.Count131072.C015243.packed 128 cuts15243 = true := by
 decide +kernel
def pointBounds15243 : List (Nat × Nat × Nat) := [(2001874944,96479742579093,96480120752938),(2001938432,96480163264422,96480541438544)]
theorem point_links_checked15243 : (cuts15243.take 2).map (fun c => (2001862657-1+2*2^9*c.k,96479664823953+c.lower,96480042997745+c.upper)) = pointBounds15243 := by
 decide +kernel
def cuts15244 : List PrefixCut := [⟨8,54692234,54692269⟩,
⟨70,476053936,476054251⟩,
⟨128,866051078,866051651⟩]
theorem checked15244 : checkPrefixCuts (2^48) 2001993729 9 Manual.Count131072.C015244.packed 128 cuts15244 = true := by
 decide +kernel
def pointBounds15244 : List (Nat × Nat × Nat) := [(2002001920,96480586326635,96480964501028),(2002065408,96481007688337,96481385863010)]
theorem point_links_checked15244 : (cuts15244.take 2).map (fun c => (2001993729-1+2*2^9*c.k,96480531634401+c.lower,96480909808759+c.upper)) = pointBounds15244 := by
 decide +kernel
def cuts15245 : List PrefixCut := [⟨4,26711711,26711728⟩,
⟨66,443688539,443688831⟩,
⟨128,858402811,858403375⟩]
theorem checked15245 : checkPrefixCuts (2^48) 2002124801 9 Manual.Count131072.C015245.packed 128 cuts15245 = true := by
 decide +kernel
def pointBounds15245 : List (Nat × Nat × Nat) := [(2002128896,96481424397190,96481802572138),(2002192384,96481841374018,96482219549241),(2002255872,96482256088290,96482634263785)]
theorem point_links_checked15245 : (cuts15245.take 3).map (fun c => (2002124801-1+2*2^9*c.k,96481397685479+c.lower,96481775860410+c.upper)) = pointBounds15245 := by
 decide +kernel
def cuts15246 : List PrefixCut := [⟨62,414419888,414420167⟩,
⟨124,828826708,828827262⟩,
⟨128,857924661,857925234⟩]
theorem checked15246 : checkPrefixCuts (2^48) 2002255873 9 Manual.Count131072.C015246.packed 128 cuts15246 = true := by
 decide +kernel
def pointBounds15246 : List (Nat × Nat × Nat) := [(2002319360,96482670508178,96483048683952),(2002382848,96483084914998,96483463091047)]
theorem point_links_checked15246 : (cuts15246.take 2).map (fun c => (2002255873-1+2*2^9*c.k,96482256088290+c.lower,96482634263785+c.upper)) = pointBounds15246 := by
 decide +kernel
def cuts15247 : List PrefixCut := [⟨58,388107034,388107293⟩,
⟨120,809796899,809797436⟩,
⟨128,868270176,868270752⟩]
theorem checked15247 : checkPrefixCuts (2^48) 2002386945 9 Manual.Count131072.C015247.packed 128 cuts15247 = true := by
 decide +kernel
def pointBounds15247 : List (Nat × Nat × Nat) := [(2002446336,96483502119985,96483880296312),(2002509824,96483923809850,96484301986455)]
theorem point_links_checked15247 : (cuts15247.take 2).map (fun c => (2002386945-1+2*2^9*c.k,96483114012951+c.lower,96483492189019+c.upper)) = pointBounds15247 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000163
