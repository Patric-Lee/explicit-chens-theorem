import PlattAssemblyKernel
import PlattCertificates.Count131072.C015568
import PlattCertificates.Count131072.C015569
import PlattCertificates.Count131072.C015570
import PlattCertificates.Count131072.C015571
import PlattCertificates.Count131072.C015572
import PlattCertificates.Count131072.C015573
import PlattCertificates.Count131072.C015574
import PlattCertificates.Count131072.C015575
import PlattCertificates.Count131072.C015576
import PlattCertificates.Count131072.C015577
import PlattCertificates.Count131072.C015578
import PlattCertificates.Count131072.C015579
import PlattCertificates.Count131072.C015580
import PlattCertificates.Count131072.C015581
import PlattCertificates.Count131072.C015582
import PlattCertificates.Count131072.C015583
import PlattCertificates.Count131072.C015584
import PlattCertificates.Count131072.C015585
import PlattCertificates.Count131072.C015586
import PlattCertificates.Count131072.C015587
import PlattCertificates.Count131072.C015588
import PlattCertificates.Count131072.C015589
import PlattCertificates.Count131072.C015590
import PlattCertificates.Count131072.C015591
import PlattCertificates.Count131072.C015592
import PlattCertificates.Count131072.C015593
import PlattCertificates.Count131072.C015594
import PlattCertificates.Count131072.C015595
import PlattCertificates.Count131072.C015596
import PlattCertificates.Count131072.C015597
import PlattCertificates.Count131072.C015598
import PlattCertificates.Count131072.C015599
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000174
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15568 : List PrefixCut := [⟨27,181732170,181732287⟩,
⟨90,596540243,596540631⟩,
⟨128,844344996,844345544⟩]
theorem checked15568 : checkPrefixCuts (2^48) 2044461057 9 Manual.Count131072.C015568.packed 128 cuts15568 = true := by
 decide +kernel
def pointBounds15568 : List (Nat × Nat × Nat) := [(2044488704,96756475433660,96756853789327),(2044553216,96756890241733,96757268597671)]
theorem point_links_checked15568 : (cuts15568.take 2).map (fun c => (2044461057-1+2*2^9*c.k,96756293701490+c.lower,96756672057040+c.upper)) = pointBounds15568 := by
 decide +kernel
def cuts15569 : List PrefixCut := [⟨25,167265562,167265670⟩,
⟨88,577779928,577780303⟩,
⟨128,844015412,844015959⟩]
theorem checked15569 : checkPrefixCuts (2^48) 2044592129 9 Manual.Count131072.C015569.packed 128 cuts15569 = true := by
 decide +kernel
def pointBounds15569 : List (Nat × Nat × Nat) := [(2044617728,96757305312048,96757683668254),(2044682240,96757715826414,96758094182887)]
theorem point_links_checked15569 : (cuts15569.take 2).map (fun c => (2044592129-1+2*2^9*c.k,96757138046486+c.lower,96757516402584+c.upper)) = pointBounds15569 := by
 decide +kernel
def cuts15570 : List PrefixCut := [⟨23,147707428,147707525⟩,
⟨86,559297080,559297449⟩,
⟨128,838041982,838042528⟩]
theorem checked15570 : checkPrefixCuts (2^48) 2044723201 9 Manual.Count131072.C015570.packed 128 cuts15570 = true := by
 decide +kernel
def pointBounds15570 : List (Nat × Nat × Nat) := [(2044746752,96758129769326,96758508126068),(2044811264,96758541358978,96758919715992)]
theorem point_links_checked15570 : (cuts15570.take 2).map (fun c => (2044723201-1+2*2^9*c.k,96757982061898+c.lower,96758360418543+c.upper)) = pointBounds15570 := by
 decide +kernel
def cuts15571 : List PrefixCut := [⟨21,137924921,137925011⟩,
⟨84,550452161,550452525⟩,
⟨128,842255395,842255950⟩]
theorem checked15571 : checkPrefixCuts (2^48) 2044854273 9 Manual.Count131072.C015571.packed 128 cuts15571 = true := by
 decide +kernel
def pointBounds15571 : List (Nat × Nat × Nat) := [(2044875776,96758958028801,96759336386082),(2044940288,96759370556041,96759748913596)]
theorem point_links_checked15571 : (cuts15571.take 2).map (fun c => (2044854273-1+2*2^9*c.k,96758820103880+c.lower,96759198461071+c.upper)) = pointBounds15571 := by
 decide +kernel
def cuts15572 : List PrefixCut := [⟨19,118646424,118646504⟩,
⟨82,542846832,542847188⟩,
⟨128,841100381,841100936⟩]
theorem checked15572 : checkPrefixCuts (2^48) 2044985345 9 Manual.Count131072.C015572.packed 128 cuts15572 = true := by
 decide +kernel
def pointBounds15572 : List (Nat × Nat × Nat) := [(2045004800,96759781005699,96760159363525),(2045069312,96760205206107,96760583564209)]
theorem point_links_checked15572 : (cuts15572.take 2).map (fun c => (2044985345-1+2*2^9*c.k,96759662359275+c.lower,96760040717021+c.upper)) = pointBounds15572 := by
 decide +kernel
def cuts15573 : List PrefixCut := [⟨17,113271229,113271305⟩,
⟨80,524094882,524095231⟩,
⟨128,842147478,842148031⟩]
theorem checked15573 : checkPrefixCuts (2^48) 2045116417 9 Manual.Count131072.C015573.packed 128 cuts15573 = true := by
 decide +kernel
def pointBounds15573 : List (Nat × Nat × Nat) := [(2045133824,96760616730885,96760995089262),(2045198336,96761027554538,96761405913188)]
theorem point_links_checked15573 : (cuts15573.take 2).map (fun c => (2045116417-1+2*2^9*c.k,96760503459656+c.lower,96760881817957+c.upper)) = pointBounds15573 := by
 decide +kernel
def cuts15574 : List PrefixCut := [⟨15,100327423,100327491⟩,
⟨78,508647984,508648321⟩,
⟨128,840854825,840855378⟩]
theorem checked15574 : checkPrefixCuts (2^48) 2045247489 9 Manual.Count131072.C015574.packed 128 cuts15574 = true := by
 decide +kernel
def pointBounds15574 : List (Nat × Nat × Nat) := [(2045262848,96761445934557,96761824293479),(2045327360,96761854255118,96762232614309)]
theorem point_links_checked15574 : (cuts15574.take 2).map (fun c => (2045247489-1+2*2^9*c.k,96761345607134+c.lower,96761723965988+c.upper)) = pointBounds15574 := by
 decide +kernel
def cuts15575 : List PrefixCut := [⟨13,86284353,86284409⟩,
⟨76,511642919,511643252⟩,
⟨128,850021036,850021587⟩]
theorem checked15575 : checkPrefixCuts (2^48) 2045378561 9 Manual.Count131072.C015575.packed 128 cuts15575 = true := by
 decide +kernel
def pointBounds15575 : List (Nat × Nat × Nat) := [(2045391872,96762272746312,96762651105775),(2045456384,96762698104878,96763076464618)]
theorem point_links_checked15575 : (cuts15575.take 2).map (fun c => (2045378561-1+2*2^9*c.k,96762186461959+c.lower,96762564821366+c.upper)) = pointBounds15575 := by
 decide +kernel
def cuts15576 : List PrefixCut := [⟨11,72793497,72793544⟩,
⟨74,483126526,483126842⟩,
⟨128,843223875,843224425⟩]
theorem checked15576 : checkPrefixCuts (2^48) 2045509633 9 Manual.Count131072.C015576.packed 128 cuts15576 = true := by
 decide +kernel
def pointBounds15576 : List (Nat × Nat × Nat) := [(2045520896,96763109276492,96763487636497),(2045585408,96763519609521,96763897969795)]
theorem point_links_checked15576 : (cuts15576.take 2).map (fun c => (2045509633-1+2*2^9*c.k,96763036482995+c.lower,96763414842953+c.upper)) = pointBounds15576 := by
 decide +kernel
def cuts15577 : List PrefixCut := [⟨9,60129939,60129977⟩,
⟨72,478555261,478555572⟩,
⟨128,845371635,845372184⟩]
theorem checked15577 : checkPrefixCuts (2^48) 2045640705 9 Manual.Count131072.C015577.packed 128 cuts15577 = true := by
 decide +kernel
def pointBounds15577 : List (Nat × Nat × Nat) := [(2045649920,96763939836809,96764318197355),(2045714432,96764358262131,96764736622950)]
theorem point_links_checked15577 : (cuts15577.take 2).map (fun c => (2045640705-1+2*2^9*c.k,96763879706870+c.lower,96764258067378+c.upper)) = pointBounds15577 := by
 decide +kernel
def cuts15578 : List PrefixCut := [⟨7,47055221,47055251⟩,
⟨70,459950591,459950891⟩,
⟨128,839126004,839126551⟩]
theorem checked15578 : checkPrefixCuts (2^48) 2045771777 9 Manual.Count131072.C015578.packed 128 cuts15578 = true := by
 decide +kernel
def pointBounds15578 : List (Nat × Nat × Nat) := [(2045778944,96764772133726,96765150494813),(2045843456,96765185029096,96765563390453)]
theorem point_links_checked15578 : (cuts15578.take 2).map (fun c => (2045771777-1+2*2^9*c.k,96764725078505+c.lower,96765103439562+c.upper)) = pointBounds15578 := by
 decide +kernel
def cuts15579 : List PrefixCut := [⟨5,34532481,34532506⟩,
⟨68,441073340,441073635⟩,
⟨128,837008575,837009126⟩]
theorem checked15579 : checkPrefixCuts (2^48) 2045902849 9 Manual.Count131072.C015579.packed 128 cuts15579 = true := by
 decide +kernel
def pointBounds15579 : List (Nat × Nat × Nat) := [(2045907968,96765598736990,96765977098619),(2045972480,96766005277849,96766383639748)]
theorem point_links_checked15579 : (cuts15579.take 2).map (fun c => (2045902849-1+2*2^9*c.k,96765564204509+c.lower,96765942566113+c.upper)) = pointBounds15579 := by
 decide +kernel
def cuts15580 : List PrefixCut := [⟨3,17746643,17746654⟩,
⟨66,427563583,427563855⟩,
⟨128,837367625,837368161⟩]
theorem checked15580 : checkPrefixCuts (2^48) 2046033921 9 Manual.Count131072.C015580.packed 128 cuts15580 = true := by
 decide +kernel
def pointBounds15580 : List (Nat × Nat × Nat) := [(2046036992,96766418959727,96766797321893),(2046101504,96766828776667,96767207139094)]
theorem point_links_checked15580 : (cuts15580.take 2).map (fun c => (2046033921-1+2*2^9*c.k,96766401213084+c.lower,96766779575239+c.upper)) = pointBounds15580 := by
 decide +kernel
def cuts15581 : List PrefixCut := [⟨1,6878107,6878111⟩,
⟨64,423684691,423684965⟩,
⟨127,835526113,835526655⟩,
⟨128,841853569,841854115⟩]
theorem checked15581 : checkPrefixCuts (2^48) 2046164993 9 Manual.Count131072.C015581.packed 128 cuts15581 = true := by
 decide +kernel
def pointBounds15581 : List (Nat × Nat × Nat) := [(2046166016,96767245458816,96767623821511),(2046230528,96767662265400,96768040628365),(2046295040,96768074106822,96768452470055)]
theorem point_links_checked15581 : (cuts15581.take 3).map (fun c => (2046164993-1+2*2^9*c.k,96767238580709+c.lower,96767616943400+c.upper)) = pointBounds15581 := by
 decide +kernel
def cuts15582 : List PrefixCut := [⟨62,407564312,407564577⟩,
⟨125,817179006,817179542⟩,
⟨128,835885078,835885626⟩]
theorem checked15582 : checkPrefixCuts (2^48) 2046296065 9 Manual.Count131072.C015582.packed 128 cuts15582 = true := by
 decide +kernel
def pointBounds15582 : List (Nat × Nat × Nat) := [(2046359552,96768487998590,96768866362092),(2046424064,96768897613284,96769275977057)]
theorem point_links_checked15582 : (cuts15582.take 2).map (fun c => (2046296065-1+2*2^9*c.k,96768080434278+c.lower,96768458797515+c.upper)) = pointBounds15582 := by
 decide +kernel
def cuts15583 : List PrefixCut := [⟨60,392133586,392133839⟩,
⟨123,812450478,812451006⟩,
⟨128,845046488,845047037⟩]
theorem checked15583 : checkPrefixCuts (2^48) 2046427137 9 Manual.Count131072.C015583.packed 128 cuts15583 = true := by
 decide +kernel
def pointBounds15583 : List (Nat × Nat × Nat) := [(2046488576,96769308452942,96769686816980),(2046553088,96769728769834,96770107134147)]
theorem point_links_checked15583 : (cuts15583.take 2).map (fun c => (2046427137-1+2*2^9*c.k,96768916319356+c.lower,96769294683141+c.upper)) = pointBounds15583 := by
 decide +kernel
def cuts15584 : List PrefixCut := [⟨58,384956900,384957148⟩,
⟨121,797820728,797821251⟩,
⟨128,844855020,844855574⟩]
theorem checked15584 : checkPrefixCuts (2^48) 2046558209 9 Manual.Count131072.C015584.packed 128 cuts15584 = true := by
 decide +kernel
def pointBounds15584 : List (Nat × Nat × Nat) := [(2046617600,96770146322744,96770524687326),(2046682112,96770559186572,96770937551429)]
theorem point_links_checked15584 : (cuts15584.take 2).map (fun c => (2046558209-1+2*2^9*c.k,96769761365844+c.lower,96770139730178+c.upper)) = pointBounds15584 := by
 decide +kernel
def cuts15585 : List PrefixCut := [⟨56,364441248,364441486⟩,
⟨119,783605053,783605564⟩,
⟨128,843013016,843013564⟩]
theorem checked15585 : checkPrefixCuts (2^48) 2046689281 9 Manual.Count131072.C015585.packed 128 cuts15585 = true := by
 decide +kernel
def pointBounds15585 : List (Nat × Nat × Nat) := [(2046746624,96770970662112,96771349027238),(2046811136,96771389825917,96771768191316)]
theorem point_links_checked15585 : (cuts15585.take 2).map (fun c => (2046689281-1+2*2^9*c.k,96770606220864+c.lower,96770984585752+c.upper)) = pointBounds15585 := by
 decide +kernel
def cuts15586 : List PrefixCut := [⟨54,351766603,351766832⟩,
⟨117,762928152,762928657⟩,
⟨128,834983237,834983790⟩]
theorem checked15586 : checkPrefixCuts (2^48) 2046820353 9 Manual.Count131072.C015586.packed 128 cuts15586 = true := by
 decide +kernel
def pointBounds15586 : List (Nat × Nat × Nat) := [(2046875648,96771801000483,96772179366148),(2046940160,96772212162032,96772590527973)]
theorem point_links_checked15586 : (cuts15586.take 2).map (fun c => (2046820353-1+2*2^9*c.k,96771449233880+c.lower,96771827599316+c.upper)) = pointBounds15586 := by
 decide +kernel
def cuts15587 : List PrefixCut := [⟨52,342393692,342393916⟩,
⟨115,746929207,746929694⟩,
⟨128,831904805,831905347⟩]
theorem checked15587 : checkPrefixCuts (2^48) 2046951425 9 Manual.Count131072.C015587.packed 128 cuts15587 = true := by
 decide +kernel
def pointBounds15587 : List (Nat × Nat × Nat) := [(2047004672,96772626610809,96773004977022),(2047069184,96773031146324,96773409512800)]
theorem point_links_checked15587 : (cuts15587.take 2).map (fun c => (2046951425-1+2*2^9*c.k,96772284217117+c.lower,96772662583106+c.upper)) = pointBounds15587 := by
 decide +kernel
def cuts15588 : List PrefixCut := [⟨50,335084597,335084814⟩,
⟨113,759118853,759119347⟩,
⟨128,853438522,853439077⟩]
theorem checked15588 : checkPrefixCuts (2^48) 2047082497 9 Manual.Count131072.C015588.packed 128 cuts15588 = true := by
 decide +kernel
def pointBounds15588 : List (Nat × Nat × Nat) := [(2047133696,96773451206519,96773829573267),(2047198208,96773875240775,96774253607800)]
theorem point_links_checked15588 : (cuts15588.take 2).map (fun c => (2047082497-1+2*2^9*c.k,96773116121922+c.lower,96773494488453+c.upper)) = pointBounds15588 := by
 decide +kernel
def cuts15589 : List PrefixCut := [⟨48,318839409,318839614⟩,
⟨111,730748180,730748655⟩,
⟨128,839635100,839635644⟩]
theorem checked15589 : checkPrefixCuts (2^48) 2047213569 9 Manual.Count131072.C015589.packed 128 cuts15589 = true := by
 decide +kernel
def pointBounds15589 : List (Nat × Nat × Nat) := [(2047262720,96774288399853,96774666767144),(2047327232,96774700308624,96775078676185)]
theorem point_links_checked15589 : (cuts15589.take 2).map (fun c => (2047213569-1+2*2^9*c.k,96773969560444+c.lower,96774347927530+c.upper)) = pointBounds15589 := by
 decide +kernel
def cuts15590 : List PrefixCut := [⟨46,303696251,303696447⟩,
⟨109,716541420,716541891⟩,
⟨128,841368501,841369052⟩]
theorem checked15590 : checkPrefixCuts (2^48) 2047344641 9 Manual.Count131072.C015590.packed 128 cuts15590 = true := by
 decide +kernel
def pointBounds15590 : List (Nat × Nat × Nat) := [(2047391744,96775112891795,96775491259621),(2047456256,96775525736964,96775904105065)]
theorem point_links_checked15590 : (cuts15590.take 2).map (fun c => (2047344641-1+2*2^9*c.k,96774809195544+c.lower,96775187563174+c.upper)) = pointBounds15590 := by
 decide +kernel
def cuts15591 : List PrefixCut := [⟨44,285805449,285805635⟩,
⟨107,696562533,696562990⟩,
⟨128,835678159,835678707⟩]
theorem checked15591 : checkPrefixCuts (2^48) 2047475713 9 Manual.Count131072.C015591.packed 128 cuts15591 = true := by
 decide +kernel
def pointBounds15591 : List (Nat × Nat × Nat) := [(2047520768,96775936369494,96776314737861),(2047585280,96776347126578,96776725495216)]
theorem point_links_checked15591 : (cuts15591.take 2).map (fun c => (2047475713-1+2*2^9*c.k,96775650564045+c.lower,96776028932226+c.upper)) = pointBounds15591 := by
 decide +kernel
def cuts15592 : List PrefixCut := [⟨42,270253936,270254111⟩,
⟨105,688133127,688133574⟩,
⟨128,838648863,838649411⟩]
theorem checked15592 : checkPrefixCuts (2^48) 2047606785 9 Manual.Count131072.C015592.packed 128 cuts15592 = true := by
 decide +kernel
def pointBounds15592 : List (Nat × Nat × Nat) := [(2047649792,96776756496140,96777134865044),(2047714304,96777174375331,96777552744507)]
theorem point_links_checked15592 : (cuts15592.take 2).map (fun c => (2047606785-1+2*2^9*c.k,96776486242204+c.lower,96776864610933+c.upper)) = pointBounds15592 := by
 decide +kernel
def cuts15593 : List PrefixCut := [⟨40,268724781,268724959⟩,
⟨103,675581514,675581957⟩,
⟨128,838870420,838870967⟩]
theorem checked15593 : checkPrefixCuts (2^48) 2047737857 9 Manual.Count131072.C015593.packed 128 cuts15593 = true := by
 decide +kernel
def pointBounds15593 : List (Nat × Nat × Nat) := [(2047778816,96777593615848,96777971985303),(2047843328,96778000472581,96778378842301)]
theorem point_links_checked15593 : (cuts15593.take 2).map (fun c => (2047737857-1+2*2^9*c.k,96777324891067+c.lower,96777703260344+c.upper)) = pointBounds15593 := by
 decide +kernel
def cuts15594 : List PrefixCut := [⟨38,249465177,249465342⟩,
⟨101,655334163,655334595⟩,
⟨128,832631538,832632088⟩]
theorem checked15594 : checkPrefixCuts (2^48) 2047868929 9 Manual.Count131072.C015594.packed 128 cuts15594 = true := by
 decide +kernel
def pointBounds15594 : List (Nat × Nat × Nat) := [(2047907840,96778413226664,96778791596653),(2047972352,96778819095650,96779197465906)]
theorem point_links_checked15594 : (cuts15594.take 2).map (fun c => (2047868929-1+2*2^9*c.k,96778163761487+c.lower,96778542131311+c.upper)) = pointBounds15594 := by
 decide +kernel
def cuts15595 : List PrefixCut := [⟨36,233781443,233781595⟩,
⟨99,646221735,646222154⟩,
⟨128,836563847,836564387⟩]
theorem checked15595 : checkPrefixCuts (2^48) 2048000001 9 Manual.Count131072.C015595.packed 128 cuts15595 = true := by
 decide +kernel
def pointBounds15595 : List (Nat × Nat × Nat) := [(2048036864,96779230174468,96779608544994),(2048101376,96779642614760,96780020985553)]
theorem point_links_checked15595 : (cuts15595.take 2).map (fun c => (2048000001-1+2*2^9*c.k,96778996393025+c.lower,96779374763399+c.upper)) = pointBounds15595 := by
 decide +kernel
def cuts15596 : List PrefixCut := [⟨34,218786874,218787015⟩,
⟨97,637522667,637523080⟩,
⟨128,842556855,842557400⟩]
theorem checked15596 : checkPrefixCuts (2^48) 2048131073 9 Manual.Count131072.C015596.packed 128 cuts15596 = true := by
 decide +kernel
def pointBounds15596 : List (Nat × Nat × Nat) := [(2048165888,96780051743746,96780430114801),(2048230400,96780470479539,96780848850866)]
theorem point_links_checked15596 : (cuts15596.take 2).map (fun c => (2048131073-1+2*2^9*c.k,96779832956872+c.lower,96780211327786+c.upper)) = pointBounds15596 := by
 decide +kernel
def cuts15597 : List PrefixCut := [⟨32,209978081,209978220⟩,
⟨95,624702452,624702861⟩,
⟨128,842365703,842366251⟩]
theorem checked15597 : checkPrefixCuts (2^48) 2048262145 9 Manual.Count131072.C015597.packed 128 cuts15597 = true := by
 decide +kernel
def pointBounds15597 : List (Nat × Nat × Nat) := [(2048294912,96780885491808,96781263863406),(2048359424,96781300216179,96781678588047)]
theorem point_links_checked15597 : (cuts15597.take 2).map (fun c => (2048262145-1+2*2^9*c.k,96780675513727+c.lower,96781053885186+c.upper)) = pointBounds15597 := by
 decide +kernel
def cuts15598 : List PrefixCut := [⟨30,195399119,195399242⟩,
⟨93,606387417,606387807⟩,
⟨128,838052117,838052656⟩]
theorem checked15598 : checkPrefixCuts (2^48) 2048393217 9 Manual.Count131072.C015598.packed 128 cuts15598 = true := by
 decide +kernel
def pointBounds15598 : List (Nat × Nat × Nat) := [(2048423936,96781713278549,96782091650679),(2048488448,96782124266847,96782502639244)]
theorem point_links_checked15598 : (cuts15598.take 2).map (fun c => (2048393217-1+2*2^9*c.k,96781517879430+c.lower,96781896251437+c.upper)) = pointBounds15598 := by
 decide +kernel
def cuts15599 : List PrefixCut := [⟨28,187279966,187280090⟩,
⟨91,602639037,602639433⟩,
⟨128,844044201,844044754⟩]
theorem checked15599 : checkPrefixCuts (2^48) 2048524289 9 Manual.Count131072.C015599.packed 128 cuts15599 = true := by
 decide +kernel
def pointBounds15599 : List (Nat × Nat × Nat) := [(2048552960,96782543211513,96782921584183),(2048617472,96782958570584,96783336943526)]
theorem point_links_checked15599 : (cuts15599.take 2).map (fun c => (2048524289-1+2*2^9*c.k,96782355931547+c.lower,96782734304093+c.upper)) = pointBounds15599 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000174
