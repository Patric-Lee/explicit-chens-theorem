import PlattAssemblyKernel
import PlattCertificates.Count131072.C038224
import PlattCertificates.Count131072.C038225
import PlattCertificates.Count131072.C038226
import PlattCertificates.Count131072.C038227
import PlattCertificates.Count131072.C038228
import PlattCertificates.Count131072.C038229
import PlattCertificates.Count131072.C038230
import PlattCertificates.Count131072.C038231
import PlattCertificates.Count131072.C038232
import PlattCertificates.Count131072.C038233
import PlattCertificates.Count131072.C038234
import PlattCertificates.Count131072.C038235
import PlattCertificates.Count131072.C038236
import PlattCertificates.Count131072.C038237
import PlattCertificates.Count131072.C038238
import PlattCertificates.Count131072.C038239
import PlattCertificates.Count131072.C038240
import PlattCertificates.Count131072.C038241
import PlattCertificates.Count131072.C038242
import PlattCertificates.Count131072.C038243
import PlattCertificates.Count131072.C038244
import PlattCertificates.Count131072.C038245
import PlattCertificates.Count131072.C038246
import PlattCertificates.Count131072.C038247
import PlattCertificates.Count131072.C038248
import PlattCertificates.Count131072.C038249
import PlattCertificates.Count131072.C038250
import PlattCertificates.Count131072.C038251
import PlattCertificates.Count131072.C038252
import PlattCertificates.Count131072.C038253
import PlattCertificates.Count131072.C038254
import PlattCertificates.Count131072.C038255
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000257
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts38224 : List PrefixCut := [⟨64,329466540,329466741⟩]
theorem checked38224 : checkPrefixCuts (2^48) 5014028289 10 Manual.Count131072.C038224.packed 64 cuts38224 = true := by
 decide +kernel
def cuts38225 : List PrefixCut := [⟨3,15156713,15156721⟩,
⟨64,329121093,329121289⟩]
theorem checked38225 : checkPrefixCuts (2^48) 5014159361 10 Manual.Count131072.C038225.packed 64 cuts38225 = true := by
 decide +kernel
def pointBounds38225 : List (Nat × Nat × Nat) := [(5014165504,108295257613925,108295642777943)]
theorem point_links_checked38225 : (cuts38225.take 1).map (fun c => (5014159361-1+2*2^10*c.k,108295242457212+c.lower,108295627621222+c.upper)) = pointBounds38225 := by
 decide +kernel
def cuts38226 : List PrefixCut := [⟨16,79654652,79654700⟩,
⟨64,327091676,327091871⟩]
theorem checked38226 : checkPrefixCuts (2^48) 5014290433 10 Manual.Count131072.C038226.packed 64 cuts38226 = true := by
 decide +kernel
def pointBounds38226 : List (Nat × Nat × Nat) := [(5014323200,108295651232957,108296036397211)]
theorem point_links_checked38226 : (cuts38226.take 1).map (fun c => (5014290433-1+2*2^10*c.k,108295571578305+c.lower,108295956742511+c.upper)) = pointBounds38226 := by
 decide +kernel
def cuts38227 : List PrefixCut := [⟨29,153186259,153186354⟩,
⟨64,332977094,332977296⟩]
theorem checked38227 : checkPrefixCuts (2^48) 5014421505 10 Manual.Count131072.C038227.packed 64 cuts38227 = true := by
 decide +kernel
def pointBounds38227 : List (Nat × Nat × Nat) := [(5014480896,108296051856240,108296437020736)]
theorem point_links_checked38227 : (cuts38227.take 1).map (fun c => (5014421505-1+2*2^10*c.k,108295898669981+c.lower,108296283834382+c.upper)) = pointBounds38227 := by
 decide +kernel
def cuts38228 : List PrefixCut := [⟨42,214982225,214982353⟩,
⟨64,331396662,331396859⟩]
theorem checked38228 : checkPrefixCuts (2^48) 5014552577 10 Manual.Count131072.C038228.packed 64 cuts38228 = true := by
 decide +kernel
def pointBounds38228 : List (Nat × Nat × Nat) := [(5014638592,108296446629300,108296831794031)]
theorem point_links_checked38228 : (cuts38228.take 1).map (fun c => (5014552577-1+2*2^10*c.k,108296231647075+c.lower,108296616811678+c.upper)) = pointBounds38228 := by
 decide +kernel
def cuts38229 : List PrefixCut := [⟨55,283622406,283622581⟩,
⟨64,330770575,330770778⟩]
theorem checked38229 : checkPrefixCuts (2^48) 5014683649 10 Manual.Count131072.C038229.packed 64 cuts38229 = true := by
 decide +kernel
def pointBounds38229 : List (Nat × Nat × Nat) := [(5014796288,108296846666143,108297231831118)]
theorem point_links_checked38229 : (cuts38229.take 1).map (fun c => (5014683649-1+2*2^10*c.k,108296563043737+c.lower,108296948208537+c.upper)) = pointBounds38229 := by
 decide +kernel
def cuts38230 : List PrefixCut := [⟨64,332333511,332333715⟩]
theorem checked38230 : checkPrefixCuts (2^48) 5014814721 10 Manual.Count131072.C038230.packed 64 cuts38230 = true := by
 decide +kernel
def cuts38231 : List PrefixCut := [⟨4,22057974,22057986⟩,
⟨64,330921676,330921874⟩]
theorem checked38231 : checkPrefixCuts (2^48) 5014945793 10 Manual.Count131072.C038231.packed 64 cuts38231 = true := by
 decide +kernel
def pointBounds38231 : List (Nat × Nat × Nat) := [(5014953984,108297248205797,108297633371016)]
theorem point_links_checked38231 : (cuts38231.take 1).map (fun c => (5014945793-1+2*2^10*c.k,108297226147823+c.lower,108297611313030+c.upper)) = pointBounds38231 := by
 decide +kernel
def cuts38232 : List PrefixCut := [⟨17,88285480,88285532⟩,
⟨64,330520175,330520374⟩]
theorem checked38232 : checkPrefixCuts (2^48) 5015076865 10 Manual.Count131072.C038232.packed 64 cuts38232 = true := by
 decide +kernel
def pointBounds38232 : List (Nat × Nat × Nat) := [(5015111680,108297645354979,108298030520436)]
theorem point_links_checked38232 : (cuts38232.take 1).map (fun c => (5015076865-1+2*2^10*c.k,108297557069499+c.lower,108297942234904+c.upper)) = pointBounds38232 := by
 decide +kernel
def cuts38233 : List PrefixCut := [⟨30,155687765,155687858⟩,
⟨64,327761474,327761671⟩]
theorem checked38233 : checkPrefixCuts (2^48) 5015207937 10 Manual.Count131072.C038233.packed 64 cuts38233 = true := by
 decide +kernel
def pointBounds38233 : List (Nat × Nat × Nat) := [(5015269376,108298043277439,108298428443136)]
theorem point_links_checked38233 : (cuts38233.take 1).map (fun c => (5015207937-1+2*2^10*c.k,108297887589674+c.lower,108298272755278+c.upper)) = pointBounds38233 := by
 decide +kernel
def cuts38234 : List PrefixCut := [⟨43,221683125,221683261⟩,
⟨64,330110014,330110213⟩]
theorem checked38234 : checkPrefixCuts (2^48) 5015339009 10 Manual.Count131072.C038234.packed 64 cuts38234 = true := by
 decide +kernel
def pointBounds38234 : List (Nat × Nat × Nat) := [(5015427072,108298437034273,108298822200210)]
theorem point_links_checked38234 : (cuts38234.take 1).map (fun c => (5015339009-1+2*2^10*c.k,108298215351148+c.lower,108298600516949+c.upper)) = pointBounds38234 := by
 decide +kernel
def cuts38235 : List PrefixCut := [⟨56,291098048,291098228⟩,
⟨64,331616662,331616866⟩]
theorem checked38235 : checkPrefixCuts (2^48) 5015470081 10 Manual.Count131072.C038235.packed 64 cuts38235 = true := by
 decide +kernel
def pointBounds38235 : List (Nat × Nat × Nat) := [(5015584768,108298836559210,108299221725390)]
theorem point_links_checked38235 : (cuts38235.take 1).map (fun c => (5015470081-1+2*2^10*c.k,108298545461162+c.lower,108298930627162+c.upper)) = pointBounds38235 := by
 decide +kernel
def cuts38236 : List PrefixCut := [⟨64,323639089,323639287⟩]
theorem checked38236 : checkPrefixCuts (2^48) 5015601153 10 Manual.Count131072.C038236.packed 64 cuts38236 = true := by
 decide +kernel
def cuts38237 : List PrefixCut := [⟨5,26656216,26656231⟩,
⟨64,333226730,333226930⟩]
theorem checked38237 : checkPrefixCuts (2^48) 5015732225 10 Manual.Count131072.C038237.packed 64 cuts38237 = true := by
 decide +kernel
def pointBounds38237 : List (Nat × Nat × Nat) := [(5015742464,108299227373129,108299612539546)]
theorem point_links_checked38237 : (cuts38237.take 1).map (fun c => (5015732225-1+2*2^10*c.k,108299200716913+c.lower,108299585883315+c.upper)) = pointBounds38237 := by
 decide +kernel
def cuts38238 : List PrefixCut := [⟨18,91863093,91863145⟩,
⟨64,330131601,330131800⟩]
theorem checked38238 : checkPrefixCuts (2^48) 5015863297 10 Manual.Count131072.C038238.packed 64 cuts38238 = true := by
 decide +kernel
def pointBounds38238 : List (Nat × Nat × Nat) := [(5015900160,108299625806736,108300010973390)]
theorem point_links_checked38238 : (cuts38238.take 1).map (fun c => (5015863297-1+2*2^10*c.k,108299533943643+c.lower,108299919110245+c.upper)) = pointBounds38238 := by
 decide +kernel
def cuts38239 : List PrefixCut := [⟨31,160433124,160433221⟩,
⟨64,329505766,329505966⟩]
theorem checked38239 : checkPrefixCuts (2^48) 5015994369 10 Manual.Count131072.C038239.packed 64 cuts38239 = true := by
 decide +kernel
def pointBounds38239 : List (Nat × Nat × Nat) := [(5016057856,108300024508368,108300409675266)]
theorem point_links_checked38239 : (cuts38239.take 1).map (fun c => (5015994369-1+2*2^10*c.k,108299864075244+c.lower,108300249242045+c.upper)) = pointBounds38239 := by
 decide +kernel
def cuts38240 : List PrefixCut := [⟨44,230682626,230682762⟩,
⟨64,333256765,333256963⟩]
theorem checked38240 : checkPrefixCuts (2^48) 5016125441 10 Manual.Count131072.C038240.packed 64 cuts38240 = true := by
 decide +kernel
def pointBounds38240 : List (Nat × Nat × Nat) := [(5016215552,108300424263636,108300809430773)]
theorem point_links_checked38240 : (cuts38240.take 1).map (fun c => (5016125441-1+2*2^10*c.k,108300193581010+c.lower,108300578748011+c.upper)) = pointBounds38240 := by
 decide +kernel
def cuts38241 : List PrefixCut := [⟨57,294194589,294194768⟩,
⟨64,330835171,330835373⟩]
theorem checked38241 : checkPrefixCuts (2^48) 5016256513 10 Manual.Count131072.C038241.packed 64 cuts38241 = true := by
 decide +kernel
def pointBounds38241 : List (Nat × Nat × Nat) := [(5016373248,108300821032364,108301206199742)]
theorem point_links_checked38241 : (cuts38241.take 1).map (fun c => (5016256513-1+2*2^10*c.k,108300526837775+c.lower,108300912004974+c.upper)) = pointBounds38241 := by
 decide +kernel
def cuts38242 : List PrefixCut := [⟨64,329984917,329985115⟩]
theorem checked38242 : checkPrefixCuts (2^48) 5016387585 10 Manual.Count131072.C038242.packed 64 cuts38242 = true := by
 decide +kernel
def cuts38243 : List PrefixCut := [⟨6,29738056,29738074⟩,
⟨64,325319276,325319474⟩]
theorem checked38243 : checkPrefixCuts (2^48) 5016518657 10 Manual.Count131072.C038243.packed 64 cuts38243 = true := by
 decide +kernel
def pointBounds38243 : List (Nat × Nat × Nat) := [(5016530944,108301217395919,108301602563536)]
theorem point_links_checked38243 : (cuts38243.take 1).map (fun c => (5016518657-1+2*2^10*c.k,108301187657863+c.lower,108301572825462+c.upper)) = pointBounds38243 := by
 decide +kernel
def cuts38244 : List PrefixCut := [⟨19,101611453,101611513⟩,
⟨64,336307851,336308054⟩]
theorem checked38244 : checkPrefixCuts (2^48) 5016649729 10 Manual.Count131072.C038244.packed 64 cuts38244 = true := by
 decide +kernel
def pointBounds38244 : List (Nat × Nat × Nat) := [(5016688640,108301614588592,108301999756449)]
theorem point_links_checked38244 : (cuts38244.take 1).map (fun c => (5016649729-1+2*2^10*c.k,108301512977139+c.lower,108301898144936+c.upper)) = pointBounds38244 := by
 decide +kernel
def cuts38245 : List PrefixCut := [⟨32,167252918,167253020⟩,
⟨64,333381531,333381735⟩]
theorem checked38245 : checkPrefixCuts (2^48) 5016780801 10 Manual.Count131072.C038245.packed 64 cuts38245 = true := by
 decide +kernel
def pointBounds38245 : List (Nat × Nat × Nat) := [(5016846336,108302016537908,108302401706010)]
theorem point_links_checked38245 : (cuts38245.take 1).map (fun c => (5016780801-1+2*2^10*c.k,108301849284990+c.lower,108302234452990+c.upper)) = pointBounds38245 := by
 decide +kernel
def cuts38246 : List PrefixCut := [⟨45,226662985,226663126⟩,
⟨64,327257392,327257593⟩]
theorem checked38246 : checkPrefixCuts (2^48) 5016911873 10 Manual.Count131072.C038246.packed 64 cuts38246 = true := by
 decide +kernel
def pointBounds38246 : List (Nat × Nat × Nat) := [(5017004032,108302409329506,108302794497851)]
theorem point_links_checked38246 : (cuts38246.take 1).map (fun c => (5016911873-1+2*2^10*c.k,108302182666521+c.lower,108302567834725+c.upper)) = pointBounds38246 := by
 decide +kernel
def cuts38247 : List PrefixCut := [⟨58,296785266,296785444⟩,
⟨64,326463406,326463603⟩]
theorem checked38247 : checkPrefixCuts (2^48) 5017042945 10 Manual.Count131072.C038247.packed 64 cuts38247 = true := by
 decide +kernel
def pointBounds38247 : List (Nat × Nat × Nat) := [(5017161728,108302806709179,108303191877762)]
theorem point_links_checked38247 : (cuts38247.take 1).map (fun c => (5017042945-1+2*2^10*c.k,108302509923913+c.lower,108302895092318+c.upper)) = pointBounds38247 := by
 decide +kernel
def cuts38248 : List PrefixCut := [⟨64,331447926,331448124⟩]
theorem checked38248 : checkPrefixCuts (2^48) 5017174017 10 Manual.Count131072.C038248.packed 64 cuts38248 = true := by
 decide +kernel
def cuts38249 : List PrefixCut := [⟨7,36633778,36633800⟩,
⟨64,328073263,328073463⟩]
theorem checked38249 : checkPrefixCuts (2^48) 5017305089 10 Manual.Count131072.C038249.packed 64 cuts38249 = true := by
 decide +kernel
def pointBounds38249 : List (Nat × Nat × Nat) := [(5017319424,108303204469023,108303589637845)]
theorem point_links_checked38249 : (cuts38249.take 1).map (fun c => (5017305089-1+2*2^10*c.k,108303167835245+c.lower,108303553004045+c.upper)) = pointBounds38249 := by
 decide +kernel
def cuts38250 : List PrefixCut := [⟨20,103895570,103895632⟩,
⟨64,332328177,332328375⟩]
theorem checked38250 : checkPrefixCuts (2^48) 5017436161 10 Manual.Count131072.C038250.packed 64 cuts38250 = true := by
 decide +kernel
def pointBounds38250 : List (Nat × Nat × Nat) := [(5017477120,108303599804078,108303984973140)]
theorem point_links_checked38250 : (cuts38250.take 1).map (fun c => (5017436161-1+2*2^10*c.k,108303495908508+c.lower,108303881077508+c.upper)) = pointBounds38250 := by
 decide +kernel
def cuts38251 : List PrefixCut := [⟨33,173060795,173060905⟩,
⟨64,335404839,335405045⟩]
theorem checked38251 : checkPrefixCuts (2^48) 5017567233 10 Manual.Count131072.C038251.packed 64 cuts38251 = true := by
 decide +kernel
def pointBounds38251 : List (Nat × Nat × Nat) := [(5017634816,108304001297480,108304386466788)]
theorem point_links_checked38251 : (cuts38251.take 1).map (fun c => (5017567233-1+2*2^10*c.k,108303828236685+c.lower,108304213405883+c.upper)) = pointBounds38251 := by
 decide +kernel
def cuts38252 : List PrefixCut := [⟨46,238463644,238463786⟩,
⟨64,330179222,330179420⟩]
theorem checked38252 : checkPrefixCuts (2^48) 5017698305 10 Manual.Count131072.C038252.packed 64 cuts38252 = true := by
 decide +kernel
def pointBounds38252 : List (Nat × Nat × Nat) := [(5017792512,108304402105168,108304787274714)]
theorem point_links_checked38252 : (cuts38252.take 1).map (fun c => (5017698305-1+2*2^10*c.k,108304163641524+c.lower,108304548810928+c.upper)) = pointBounds38252 := by
 decide +kernel
def cuts38253 : List PrefixCut := [⟨59,298870304,298870487⟩,
⟨64,324561147,324561345⟩]
theorem checked38253 : checkPrefixCuts (2^48) 5017829377 10 Manual.Count131072.C038253.packed 64 cuts38253 = true := by
 decide +kernel
def pointBounds38253 : List (Nat × Nat × Nat) := [(5017950208,108304792691050,108305177860835)]
theorem point_links_checked38253 : (cuts38253.take 1).map (fun c => (5017829377-1+2*2^10*c.k,108304493820746+c.lower,108304878990348+c.upper)) = pointBounds38253 := by
 decide +kernel
def cuts38254 : List PrefixCut := [⟨64,327469523,327469720⟩]
theorem checked38254 : checkPrefixCuts (2^48) 5017960449 10 Manual.Count131072.C038254.packed 64 cuts38254 = true := by
 decide +kernel
def cuts38255 : List PrefixCut := [⟨8,42125040,42125066⟩,
⟨64,328358420,328358617⟩]
theorem checked38255 : checkPrefixCuts (2^48) 5018091521 10 Manual.Count131072.C038255.packed 64 cuts38255 = true := by
 decide +kernel
def pointBounds38255 : List (Nat × Nat × Nat) := [(5018107904,108305187976456,108305573146479)]
theorem point_links_checked38255 : (cuts38255.take 1).map (fun c => (5018091521-1+2*2^10*c.k,108305145851416+c.lower,108305531021413+c.upper)) = pointBounds38255 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000257
