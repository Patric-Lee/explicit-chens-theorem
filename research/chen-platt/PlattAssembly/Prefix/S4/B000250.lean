import PlattAssemblyKernel
import PlattCertificates.Count131072.C038000
import PlattCertificates.Count131072.C038001
import PlattCertificates.Count131072.C038002
import PlattCertificates.Count131072.C038003
import PlattCertificates.Count131072.C038004
import PlattCertificates.Count131072.C038005
import PlattCertificates.Count131072.C038006
import PlattCertificates.Count131072.C038007
import PlattCertificates.Count131072.C038008
import PlattCertificates.Count131072.C038009
import PlattCertificates.Count131072.C038010
import PlattCertificates.Count131072.C038011
import PlattCertificates.Count131072.C038012
import PlattCertificates.Count131072.C038013
import PlattCertificates.Count131072.C038014
import PlattCertificates.Count131072.C038015
import PlattCertificates.Count131072.C038016
import PlattCertificates.Count131072.C038017
import PlattCertificates.Count131072.C038018
import PlattCertificates.Count131072.C038019
import PlattCertificates.Count131072.C038020
import PlattCertificates.Count131072.C038021
import PlattCertificates.Count131072.C038022
import PlattCertificates.Count131072.C038023
import PlattCertificates.Count131072.C038024
import PlattCertificates.Count131072.C038025
import PlattCertificates.Count131072.C038026
import PlattCertificates.Count131072.C038027
import PlattCertificates.Count131072.C038028
import PlattCertificates.Count131072.C038029
import PlattCertificates.Count131072.C038030
import PlattCertificates.Count131072.C038031
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000250
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts38000 : List PrefixCut := [⟨4,20554383,20554395⟩,
⟨64,329261348,329261544⟩]
theorem checked38000 : checkPrefixCuts (2^48) 4984668161 10 Manual.Count131072.C038000.packed 64 cuts38000 = true := by
 decide +kernel
def pointBounds38000 : List (Nat × Nat × Nat) := [(4984676352,108220907435953,108221292555178)]
theorem point_links_checked38000 : (cuts38000.take 1).map (fun c => (4984668161-1+2*2^10*c.k,108220886881570+c.lower,108221272000783+c.upper)) = pointBounds38000 := by
 decide +kernel
def cuts38001 : List PrefixCut := [⟨17,88934654,88934707⟩,
⟨64,336536775,336536983⟩]
theorem checked38001 : checkPrefixCuts (2^48) 4984799233 10 Manual.Count131072.C038001.packed 64 cuts38001 = true := by
 decide +kernel
def pointBounds38001 : List (Nat × Nat × Nat) := [(4984834048,108221305077572,108221690197034)]
theorem point_links_checked38001 : (cuts38001.take 1).map (fun c => (4984799233-1+2*2^10*c.k,108221216142918+c.lower,108221601262327+c.upper)) = pointBounds38001 := by
 decide +kernel
def cuts38002 : List PrefixCut := [⟨30,153640749,153640846⟩,
⟨64,330034509,330034711⟩]
theorem checked38002 : checkPrefixCuts (2^48) 4984930305 10 Manual.Count131072.C038002.packed 64 cuts38002 = true := by
 decide +kernel
def pointBounds38002 : List (Nat × Nat × Nat) := [(4984991744,108221706320442,108222091440156)]
theorem point_links_checked38002 : (cuts38002.take 1).map (fun c => (4984930305-1+2*2^10*c.k,108221552679693+c.lower,108221937799310+c.upper)) = pointBounds38002 := by
 decide +kernel
def cuts38003 : List PrefixCut := [⟨43,225231608,225231750⟩,
⟨64,333583020,333583229⟩]
theorem checked38003 : checkPrefixCuts (2^48) 4985061377 10 Manual.Count131072.C038003.packed 64 cuts38003 = true := by
 decide +kernel
def pointBounds38003 : List (Nat × Nat × Nat) := [(4985149440,108222107945810,108222493065771)]
theorem point_links_checked38003 : (cuts38003.take 1).map (fun c => (4985061377-1+2*2^10*c.k,108221882714202+c.lower,108222267834021+c.upper)) = pointBounds38003 := by
 decide +kernel
def cuts38004 : List PrefixCut := [⟨56,291793240,291793415⟩,
⟨64,332670859,332671060⟩]
theorem checked38004 : checkPrefixCuts (2^48) 4985192449 10 Manual.Count131072.C038004.packed 64 cuts38004 = true := by
 decide +kernel
def pointBounds38004 : List (Nat × Nat × Nat) := [(4985307136,108222508090462,108222893210665)]
theorem point_links_checked38004 : (cuts38004.take 1).map (fun c => (4985192449-1+2*2^10*c.k,108222216297222+c.lower,108222601417250+c.upper)) = pointBounds38004 := by
 decide +kernel
def cuts38005 : List PrefixCut := [⟨64,332775004,332775207⟩]
theorem checked38005 : checkPrefixCuts (2^48) 4985323521 10 Manual.Count131072.C038005.packed 64 cuts38005 = true := by
 decide +kernel
def cuts38006 : List PrefixCut := [⟨5,26309970,26309987⟩,
⟨64,334629395,334629597⟩]
theorem checked38006 : checkPrefixCuts (2^48) 4985454593 10 Manual.Count131072.C038006.packed 64 cuts38006 = true := by
 decide +kernel
def pointBounds38006 : List (Nat × Nat × Nat) := [(4985464832,108222908053055,108223293173504)]
theorem point_links_checked38006 : (cuts38006.take 1).map (fun c => (4985454593-1+2*2^10*c.k,108222881743085+c.lower,108223266863517+c.upper)) = pointBounds38006 := by
 decide +kernel
def cuts38007 : List PrefixCut := [⟨18,90614335,90614389⟩,
⟨64,326773068,326773266⟩]
theorem checked38007 : checkPrefixCuts (2^48) 4985585665 10 Manual.Count131072.C038007.packed 64 cuts38007 = true := by
 decide +kernel
def pointBounds38007 : List (Nat × Nat × Nat) := [(4985622528,108223306986815,108223692107503)]
theorem point_links_checked38007 : (cuts38007.take 1).map (fun c => (4985585665-1+2*2^10*c.k,108223216372480+c.lower,108223601493114+c.upper)) = pointBounds38007 := by
 decide +kernel
def cuts38008 : List PrefixCut := [⟨31,160673492,160673587⟩,
⟨64,331450340,331450538⟩]
theorem checked38008 : checkPrefixCuts (2^48) 4985716737 10 Manual.Count131072.C038008.packed 64 cuts38008 = true := by
 decide +kernel
def pointBounds38008 : List (Nat × Nat × Nat) := [(4985780224,108223703819040,108224088939967)]
theorem point_links_checked38008 : (cuts38008.take 1).map (fun c => (4985716737-1+2*2^10*c.k,108223543145548+c.lower,108223928266380+c.upper)) = pointBounds38008 := by
 decide +kernel
def cuts38009 : List PrefixCut := [⟨44,228188102,228188237⟩,
⟨64,330538326,330538526⟩]
theorem checked38009 : checkPrefixCuts (2^48) 4985847809 10 Manual.Count131072.C038009.packed 64 cuts38009 = true := by
 decide +kernel
def pointBounds38009 : List (Nat × Nat × Nat) := [(4985937920,108224102783990,108224487905155)]
theorem point_links_checked38009 : (cuts38009.take 1).map (fun c => (4985847809-1+2*2^10*c.k,108223874595888+c.lower,108224259716918+c.upper)) = pointBounds38009 := by
 decide +kernel
def cuts38010 : List PrefixCut := [⟨57,293214952,293215129⟩,
⟨64,328892540,328892739⟩]
theorem checked38010 : checkPrefixCuts (2^48) 4985978881 10 Manual.Count131072.C038010.packed 64 cuts38010 = true := by
 decide +kernel
def pointBounds38010 : List (Nat × Nat × Nat) := [(4986095616,108224498349166,108224883470573)]
theorem point_links_checked38010 : (cuts38010.take 1).map (fun c => (4985978881-1+2*2^10*c.k,108224205134214+c.lower,108224590255444+c.upper)) = pointBounds38010 := by
 decide +kernel
def cuts38011 : List PrefixCut := [⟨64,333117674,333117876⟩]
theorem checked38011 : checkPrefixCuts (2^48) 4986109953 10 Manual.Count131072.C038011.packed 64 cuts38011 = true := by
 decide +kernel
def cuts38012 : List PrefixCut := [⟨6,30765384,30765403⟩,
⟨64,327859149,327859347⟩]
theorem checked38012 : checkPrefixCuts (2^48) 4986241025 10 Manual.Count131072.C038012.packed 64 cuts38012 = true := by
 decide +kernel
def pointBounds38012 : List (Nat × Nat × Nat) := [(4986253312,108224897909812,108225283031462)]
theorem point_links_checked38012 : (cuts38012.take 1).map (fun c => (4986241025-1+2*2^10*c.k,108224867144428+c.lower,108225252266059+c.upper)) = pointBounds38012 := by
 decide +kernel
def cuts38013 : List PrefixCut := [⟨19,100365643,100365704⟩,
⟨64,339535247,339535452⟩]
theorem checked38013 : checkPrefixCuts (2^48) 4986372097 10 Manual.Count131072.C038013.packed 64 cuts38013 = true := by
 decide +kernel
def pointBounds38013 : List (Nat × Nat × Nat) := [(4986411008,108225295369220,108225680491110)]
theorem point_links_checked38013 : (cuts38013.take 1).map (fun c => (4986372097-1+2*2^10*c.k,108225195003577+c.lower,108225580125406+c.upper)) = pointBounds38013 := by
 decide +kernel
def cuts38014 : List PrefixCut := [⟨32,165220303,165220406⟩,
⟨64,330664234,330664437⟩]
theorem checked38014 : checkPrefixCuts (2^48) 4986503169 10 Manual.Count131072.C038014.packed 64 cuts38014 = true := by
 decide +kernel
def pointBounds38014 : List (Nat × Nat × Nat) := [(4986568704,108225699759127,108226084881264)]
theorem point_links_checked38014 : (cuts38014.take 1).map (fun c => (4986503169-1+2*2^10*c.k,108225534538824+c.lower,108225919660858+c.upper)) = pointBounds38014 := by
 decide +kernel
def cuts38015 : List PrefixCut := [⟨45,230240576,230240711⟩,
⟨64,327946185,327946378⟩]
theorem checked38015 : checkPrefixCuts (2^48) 4986634241 10 Manual.Count131072.C038015.packed 64 cuts38015 = true := by
 decide +kernel
def pointBounds38015 : List (Nat × Nat × Nat) := [(4986726400,108226095443634,108226480566006)]
theorem point_links_checked38015 : (cuts38015.take 1).map (fun c => (4986634241-1+2*2^10*c.k,108225865203058+c.lower,108226250325295+c.upper)) = pointBounds38015 := by
 decide +kernel
def cuts38016 : List PrefixCut := [⟨58,305078265,305078452⟩,
⟨64,335952568,335952774⟩]
theorem checked38016 : checkPrefixCuts (2^48) 4986765313 10 Manual.Count131072.C038016.packed 64 cuts38016 = true := by
 decide +kernel
def pointBounds38016 : List (Nat × Nat × Nat) := [(4986884096,108226498227508,108226883350125)]
theorem point_links_checked38016 : (cuts38016.take 1).map (fun c => (4986765313-1+2*2^10*c.k,108226193149243+c.lower,108226578271673+c.upper)) = pointBounds38016 := by
 decide +kernel
def cuts38017 : List PrefixCut := [⟨64,331259030,331259229⟩]
theorem checked38017 : checkPrefixCuts (2^48) 4986896385 10 Manual.Count131072.C038017.packed 64 cuts38017 = true := by
 decide +kernel
def cuts38018 : List PrefixCut := [⟨7,34824303,34824324⟩,
⟨64,332604864,332605063⟩]
theorem checked38018 : checkPrefixCuts (2^48) 4987027457 10 Manual.Count131072.C038018.packed 64 cuts38018 = true := by
 decide +kernel
def pointBounds38018 : List (Nat × Nat × Nat) := [(4987041792,108226895185144,108227280308000)]
theorem point_links_checked38018 : (cuts38018.take 1).map (fun c => (4987027457-1+2*2^10*c.k,108226860360841+c.lower,108227245483676+c.upper)) = pointBounds38018 := by
 decide +kernel
def cuts38019 : List PrefixCut := [⟨20,101139943,101140003⟩,
⟨64,330112819,330113014⟩]
theorem checked38019 : checkPrefixCuts (2^48) 4987158529 10 Manual.Count131072.C038019.packed 64 cuts38019 = true := by
 decide +kernel
def pointBounds38019 : List (Nat × Nat × Nat) := [(4987199488,108227294105648,108227679228742)]
theorem point_links_checked38019 : (cuts38019.take 1).map (fun c => (4987158529-1+2*2^10*c.k,108227192965705+c.lower,108227578088739+c.upper)) = pointBounds38019 := by
 decide +kernel
def cuts38020 : List PrefixCut := [⟨33,172756912,172757013⟩,
⟨64,330612129,330612323⟩]
theorem checked38020 : checkPrefixCuts (2^48) 4987289601 10 Manual.Count131072.C038020.packed 64 cuts38020 = true := by
 decide +kernel
def pointBounds38020 : List (Nat × Nat × Nat) := [(4987357184,108227695835436,108228080958766)]
theorem point_links_checked38020 : (cuts38020.take 1).map (fun c => (4987289601-1+2*2^10*c.k,108227523078524+c.lower,108227908201753+c.upper)) = pointBounds38020 := by
 decide +kernel
def cuts38021 : List PrefixCut := [⟨46,236355800,236355947⟩,
⟨64,328684595,328684798⟩]
theorem checked38021 : checkPrefixCuts (2^48) 4987420673 10 Manual.Count131072.C038021.packed 64 cuts38021 = true := by
 decide +kernel
def pointBounds38021 : List (Nat × Nat × Nat) := [(4987514880,108228090046453,108228475170023)]
theorem point_links_checked38021 : (cuts38021.take 1).map (fun c => (4987420673-1+2*2^10*c.k,108227853690653+c.lower,108228238814076+c.upper)) = pointBounds38021 := by
 decide +kernel
def cuts38022 : List PrefixCut := [⟨59,305763732,305763915⟩,
⟨64,333472854,333473053⟩]
theorem checked38022 : checkPrefixCuts (2^48) 4987551745 10 Manual.Count131072.C038022.packed 64 cuts38022 = true := by
 decide +kernel
def pointBounds38022 : List (Nat × Nat × Nat) := [(4987672576,108228488138980,108228873262789)]
theorem point_links_checked38022 : (cuts38022.take 1).map (fun c => (4987551745-1+2*2^10*c.k,108228182375248+c.lower,108228567498874+c.upper)) = pointBounds38022 := by
 decide +kernel
def cuts38023 : List PrefixCut := [⟨64,333407700,333407903⟩]
theorem checked38023 : checkPrefixCuts (2^48) 4987682817 10 Manual.Count131072.C038023.packed 64 cuts38023 = true := by
 decide +kernel
def cuts38024 : List PrefixCut := [⟨8,39784858,39784883⟩,
⟨64,330408025,330408226⟩]
theorem checked38024 : checkPrefixCuts (2^48) 4987813889 10 Manual.Count131072.C038024.packed 64 cuts38024 = true := by
 decide +kernel
def pointBounds38024 : List (Nat × Nat × Nat) := [(4987830272,108228889040660,108229274164713)]
theorem point_links_checked38024 : (cuts38024.take 1).map (fun c => (4987813889-1+2*2^10*c.k,108228849255802+c.lower,108229234379830+c.upper)) = pointBounds38024 := by
 decide +kernel
def cuts38025 : List PrefixCut := [⟨21,105920594,105920657⟩,
⟨64,334970141,334970346⟩]
theorem checked38025 : checkPrefixCuts (2^48) 4987944961 10 Manual.Count131072.C038025.packed 64 cuts38025 = true := by
 decide +kernel
def pointBounds38025 : List (Nat × Nat × Nat) := [(4987987968,108229285584421,108229670708713)]
theorem point_links_checked38025 : (cuts38025.take 1).map (fun c => (4987944961-1+2*2^10*c.k,108229179663827+c.lower,108229564788056+c.upper)) = pointBounds38025 := by
 decide +kernel
def cuts38026 : List PrefixCut := [⟨34,175268950,175269057⟩,
⟨64,329149245,329149444⟩]
theorem checked38026 : checkPrefixCuts (2^48) 4988076033 10 Manual.Count131072.C038026.packed 64 cuts38026 = true := by
 decide +kernel
def pointBounds38026 : List (Nat × Nat × Nat) := [(4988145664,108229689902918,108230075027459)]
theorem point_links_checked38026 : (cuts38026.take 1).map (fun c => (4988076033-1+2*2^10*c.k,108229514633968+c.lower,108229899758402+c.upper)) = pointBounds38026 := by
 decide +kernel
def cuts38027 : List PrefixCut := [⟨47,237954845,237954988⟩,
⟨64,324231398,324231593⟩]
theorem checked38027 : checkPrefixCuts (2^48) 4988207105 10 Manual.Count131072.C038027.packed 64 cuts38027 = true := by
 decide +kernel
def pointBounds38027 : List (Nat × Nat × Nat) := [(4988303360,108230081738058,108230466862834)]
theorem point_links_checked38027 : (cuts38027.take 1).map (fun c => (4988207105-1+2*2^10*c.k,108229843783213+c.lower,108230228907846+c.upper)) = pointBounds38027 := by
 decide +kernel
def cuts38028 : List PrefixCut := [⟨60,310793840,310794028⟩,
⟨64,330768343,330768543⟩]
theorem checked38028 : checkPrefixCuts (2^48) 4988338177 10 Manual.Count131072.C038028.packed 64 cuts38028 = true := by
 decide +kernel
def pointBounds38028 : List (Nat × Nat × Nat) := [(4988461056,108230478808451,108230863933467)]
theorem point_links_checked38028 : (cuts38028.take 1).map (fun c => (4988338177-1+2*2^10*c.k,108230168014611+c.lower,108230553139439+c.upper)) = pointBounds38028 := by
 decide +kernel
def cuts38029 : List PrefixCut := [⟨64,333919385,333919581⟩]
theorem checked38029 : checkPrefixCuts (2^48) 4988469249 10 Manual.Count131072.C038029.packed 64 cuts38029 = true := by
 decide +kernel
def cuts38030 : List PrefixCut := [⟨9,47903566,47903596⟩,
⟨64,334418423,334418625⟩]
theorem checked38030 : checkPrefixCuts (2^48) 4988600321 10 Manual.Count131072.C038030.packed 64 cuts38030 = true := by
 decide +kernel
def pointBounds38030 : List (Nat × Nat × Nat) := [(4988618752,108230880605905,108231265731159)]
theorem point_links_checked38030 : (cuts38030.take 1).map (fun c => (4988600321-1+2*2^10*c.k,108230832702339+c.lower,108231217827563+c.upper)) = pointBounds38030 := by
 decide +kernel
def cuts38031 : List PrefixCut := [⟨22,110079100,110079166⟩,
⟨64,326623435,326623629⟩]
theorem checked38031 : checkPrefixCuts (2^48) 4988731393 10 Manual.Count131072.C038031.packed 64 cuts38031 = true := by
 decide +kernel
def pointBounds38031 : List (Nat × Nat × Nat) := [(4988776448,108231277199862,108231662325354)]
theorem point_links_checked38031 : (cuts38031.take 1).map (fun c => (4988731393-1+2*2^10*c.k,108231167120762+c.lower,108231552246188+c.upper)) = pointBounds38031 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000250
