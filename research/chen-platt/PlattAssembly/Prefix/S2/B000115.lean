import PlattAssemblyKernel
import PlattCertificates.Count131072.C013680
import PlattCertificates.Count131072.C013681
import PlattCertificates.Count131072.C013682
import PlattCertificates.Count131072.C013683
import PlattCertificates.Count131072.C013684
import PlattCertificates.Count131072.C013685
import PlattCertificates.Count131072.C013686
import PlattCertificates.Count131072.C013687
import PlattCertificates.Count131072.C013688
import PlattCertificates.Count131072.C013689
import PlattCertificates.Count131072.C013690
import PlattCertificates.Count131072.C013691
import PlattCertificates.Count131072.C013692
import PlattCertificates.Count131072.C013693
import PlattCertificates.Count131072.C013694
import PlattCertificates.Count131072.C013695
import PlattCertificates.Count131072.C013696
import PlattCertificates.Count131072.C013697
import PlattCertificates.Count131072.C013698
import PlattCertificates.Count131072.C013699
import PlattCertificates.Count131072.C013700
import PlattCertificates.Count131072.C013701
import PlattCertificates.Count131072.C013702
import PlattCertificates.Count131072.C013703
import PlattCertificates.Count131072.C013704
import PlattCertificates.Count131072.C013705
import PlattCertificates.Count131072.C013706
import PlattCertificates.Count131072.C013707
import PlattCertificates.Count131072.C013708
import PlattCertificates.Count131072.C013709
import PlattCertificates.Count131072.C013710
import PlattCertificates.Count131072.C013711
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000115
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13680 : List PrefixCut := [⟨40,307160188,307160404⟩,
⟨95,718627792,718628300⟩,
⟨128,968759973,968760658⟩]
theorem checked13680 : checkPrefixCuts (2^48) 1796997121 9 Manual.Count131072.C013680.packed 128 cuts13680 = true := by
 decide +kernel
def pointBounds13680 : List (Nat × Nat × Nat) := [(1797038080,95057650661014,95058027866662),(1797094400,95058062128618,95058439334558)]
theorem point_links_checked13680 : (cuts13680.take 2).map (fun c => (1796997121-1+2*2^9*c.k,95057343500826+c.lower,95057720706258+c.upper)) = pointBounds13680 := by
 decide +kernel
def cuts13681 : List PrefixCut := [⟨22,165864637,165864751⟩,
⟨77,579499134,579499541⟩,
⟨128,973544160,973544842⟩]
theorem checked13681 : checkPrefixCuts (2^48) 1797128193 9 Manual.Count131072.C013681.packed 128 cuts13681 = true := by
 decide +kernel
def pointBounds13681 : List (Nat × Nat × Nat) := [(1797150720,95058478125436,95058855331667),(1797207040,95058891759933,95059268966457)]
theorem point_links_checked13681 : (cuts13681.take 2).map (fun c => (1797128193-1+2*2^9*c.k,95058312260799+c.lower,95058689466916+c.upper)) = pointBounds13681 := by
 decide +kernel
def cuts13682 : List PrefixCut := [⟨4,29913127,29913148⟩,
⟨59,446810518,446810829⟩,
⟨114,863381653,863382259⟩,
⟨128,972377062,972377744⟩]
theorem checked13682 : checkPrefixCuts (2^48) 1797259265 9 Manual.Count131072.C013682.packed 128 cuts13682 = true := by
 decide +kernel
def pointBounds13682 : List (Nat × Nat × Nat) := [(1797263360,95059315718086,95059692924906),(1797319680,95059732615477,95060109822587),(1797376000,95060149186612,95060526394017)]
theorem point_links_checked13682 : (cuts13682.take 3).map (fun c => (1797259265-1+2*2^9*c.k,95059285804959+c.lower,95059663011758+c.upper)) = pointBounds13682 := by
 decide +kernel
def cuts13683 : List PrefixCut := [⟨41,303177848,303178062⟩,
⟨96,710953438,710953935⟩,
⟨128,954453986,954454654⟩]
theorem checked13683 : checkPrefixCuts (2^48) 1797390337 9 Manual.Count131072.C013683.packed 128 cuts13683 = true := by
 decide +kernel
def pointBounds13683 : List (Nat × Nat × Nat) := [(1797432320,95060561359869,95060938567564),(1797488640,95060969135459,95061346343437)]
theorem point_links_checked13683 : (cuts13683.take 2).map (fun c => (1797390337-1+2*2^9*c.k,95060258182021+c.lower,95060635389502+c.upper)) = pointBounds13683 := by
 decide +kernel
def cuts13684 : List PrefixCut := [⟨23,172874863,172874985⟩,
⟨78,583756700,583757113⟩,
⟨128,963309922,963310601⟩]
theorem checked13684 : checkPrefixCuts (2^48) 1797521409 9 Manual.Count131072.C013684.packed 128 cuts13684 = true := by
 decide +kernel
def pointBounds13684 : List (Nat × Nat × Nat) := [(1797544960,95061385510870,95061762719141),(1797601280,95061796392707,95062173601269)]
theorem point_links_checked13684 : (cuts13684.take 2).map (fun c => (1797521409-1+2*2^9*c.k,95061212636007+c.lower,95061589844156+c.upper)) = pointBounds13684 := by
 decide +kernel
def cuts13685 : List PrefixCut := [⟨5,38674991,38675019⟩,
⟨60,449061229,449061544⟩,
⟨115,861470116,861470717⟩,
⟨128,958542461,958543130⟩]
theorem checked13685 : checkPrefixCuts (2^48) 1797652481 9 Manual.Count131072.C013685.packed 128 cuts13685 = true := by
 decide +kernel
def pointBounds13685 : List (Nat × Nat × Nat) := [(1797657600,95062214620920,95062591829776),(1797713920,95062625007158,95063002216301),(1797770240,95063037416045,95063414625474)]
theorem point_links_checked13685 : (cuts13685.take 3).map (fun c => (1797652481-1+2*2^9*c.k,95062175945929+c.lower,95062553154757+c.upper)) = pointBounds13685 := by
 decide +kernel
def cuts13686 : List PrefixCut := [⟨42,321899407,321899631⟩,
⟨97,738822692,738823205⟩,
⟨128,964892018,964892690⟩]
theorem checked13686 : checkPrefixCuts (2^48) 1797783553 9 Manual.Count131072.C013686.packed 128 cuts13686 = true := by
 decide +kernel
def pointBounds13686 : List (Nat × Nat × Nat) := [(1797826560,95063456387797,95063833597518),(1797882880,95063873311082,95064250521092)]
theorem point_links_checked13686 : (cuts13686.take 2).map (fun c => (1797783553-1+2*2^9*c.k,95063134488390+c.lower,95063511697887+c.upper)) = pointBounds13686 := by
 decide +kernel
def cuts13687 : List PrefixCut := [⟨24,179412312,179412438⟩,
⟨79,589734322,589734735⟩,
⟨128,953393144,953393813⟩]
theorem checked13687 : checkPrefixCuts (2^48) 1797914625 9 Manual.Count131072.C013687.packed 128 cuts13687 = true := by
 decide +kernel
def pointBounds13687 : List (Nat × Nat × Nat) := [(1797939200,95064278792720,95064656003015),(1797995520,95064689114730,95065066325312)]
theorem point_links_checked13687 : (cuts13687.take 2).map (fun c => (1797914625-1+2*2^9*c.k,95064099380408+c.lower,95064476590577+c.upper)) = pointBounds13687 := by
 decide +kernel
def cuts13688 : List PrefixCut := [⟨6,44771760,44771793⟩,
⟨61,463834380,463834702⟩,
⟨116,878344359,878344974⟩,
⟨128,968507957,968508637⟩]
theorem checked13688 : checkPrefixCuts (2^48) 1798045697 9 Manual.Count131072.C013688.packed 128 cuts13688 = true := by
 decide +kernel
def pointBounds13688 : List (Nat × Nat × Nat) := [(1798051840,95065097545312,95065474756183),(1798108160,95065516607932,95065893819092),(1798164480,95065931117911,95066308329364)]
theorem point_links_checked13688 : (cuts13688.take 3).map (fun c => (1798045697-1+2*2^9*c.k,95065052773552+c.lower,95065429984390+c.upper)) = pointBounds13688 := by
 decide +kernel
def cuts13689 : List PrefixCut := [⟨43,330438134,330438366⟩,
⟨98,739600242,739600765⟩,
⟨128,963741718,963742400⟩]
theorem checked13689 : checkPrefixCuts (2^48) 1798176769 9 Manual.Count131072.C013689.packed 128 cuts13689 = true := by
 decide +kernel
def pointBounds13689 : List (Nat × Nat × Nat) := [(1798220800,95066351719643,95066728931393),(1798277120,95066760881751,95067138093792)]
theorem point_links_checked13689 : (cuts13689.take 2).map (fun c => (1798176769-1+2*2^9*c.k,95066021281509+c.lower,95066398493027+c.upper)) = pointBounds13689 := by
 decide +kernel
def cuts13690 : List PrefixCut := [⟨25,190486016,190486148⟩,
⟨80,616996016,616996443⟩,
⟨128,977914557,977915239⟩]
theorem checked13690 : checkPrefixCuts (2^48) 1798307841 9 Manual.Count131072.C013690.packed 128 cuts13690 = true := by
 decide +kernel
def pointBounds13690 : List (Nat × Nat × Nat) := [(1798333440,95067175509243,95067552721575),(1798389760,95067602019243,95067979231870)]
theorem point_links_checked13690 : (cuts13690.take 2).map (fun c => (1798307841-1+2*2^9*c.k,95066985023227+c.lower,95067362235427+c.upper)) = pointBounds13690 := by
 decide +kernel
def cuts13691 : List PrefixCut := [⟨7,54778628,54778666⟩,
⟨62,461698306,461698635⟩,
⟨117,877838900,877839521⟩,
⟨128,959531774,959532450⟩]
theorem checked13691 : checkPrefixCuts (2^48) 1798438913 9 Manual.Count131072.C013691.packed 128 cuts13691 = true := by
 decide +kernel
def pointBounds13691 : List (Nat × Nat × Nat) := [(1798446080,95068017716412,95068394929332),(1798502400,95068424636090,95068801849301),(1798558720,95068840776684,95069217990187)]
theorem point_links_checked13691 : (cuts13691.take 3).map (fun c => (1798438913-1+2*2^9*c.k,95067962937784+c.lower,95068340150666+c.upper)) = pointBounds13691 := by
 decide +kernel
def cuts13692 : List PrefixCut := [⟨44,333026179,333026415⟩,
⟨99,746793410,746793936⟩,
⟨128,959149191,959149866⟩]
theorem checked13692 : checkPrefixCuts (2^48) 1798569985 9 Manual.Count131072.C013692.packed 128 cuts13692 = true := by
 decide +kernel
def pointBounds13692 : List (Nat × Nat × Nat) := [(1798615040,95069255495737,95069632709531),(1798671360,95069669262968,95070046477052)]
theorem point_links_checked13692 : (cuts13692.take 2).map (fun c => (1798569985-1+2*2^9*c.k,95068922469558+c.lower,95069299683116+c.upper)) = pointBounds13692 := by
 decide +kernel
def cuts13693 : List PrefixCut := [⟨26,189035939,189036072⟩,
⟨81,607941194,607941622⟩,
⟨128,964086396,964087076⟩]
theorem checked13693 : checkPrefixCuts (2^48) 1798701057 9 Manual.Count131072.C013693.packed 128 cuts13693 = true := by
 decide +kernel
def pointBounds13693 : List (Nat × Nat × Nat) := [(1798727680,95070070654688,95070447869054),(1798784000,95070489559943,95070866774604)]
theorem point_links_checked13693 : (cuts13693.take 2).map (fun c => (1798701057-1+2*2^9*c.k,95069881618749+c.lower,95070258832982+c.upper)) = pointBounds13693 := by
 decide +kernel
def cuts13694 : List PrefixCut := [⟨8,63998729,63998774⟩,
⟨63,489293150,489293496⟩,
⟨118,904403766,904404402⟩,
⟨128,979976599,979977289⟩]
theorem checked13694 : checkPrefixCuts (2^48) 1798832129 9 Manual.Count131072.C013694.packed 128 cuts13694 = true := by
 decide +kernel
def pointBounds13694 : List (Nat × Nat × Nat) := [(1798840320,95070909703874,95071286918832),(1798896640,95071334998295,95071712213554),(1798952960,95071750108911,95072127324460)]
theorem point_links_checked13694 : (cuts13694.take 3).map (fun c => (1798832129-1+2*2^9*c.k,95070845705145+c.lower,95071222920058+c.upper)) = pointBounds13694 := by
 decide +kernel
def cuts13695 : List PrefixCut := [⟨45,331545211,331545447⟩,
⟨100,742249010,742249526⟩,
⟨128,957061594,957062258⟩]
theorem checked13695 : checkPrefixCuts (2^48) 1798963201 9 Manual.Count131072.C013695.packed 128 cuts13695 = true := by
 decide +kernel
def pointBounds13695 : List (Nat × Nat × Nat) := [(1799009280,95072157226955,95072534442794),(1799065600,95072567930754,95072945146873)]
theorem point_links_checked13695 : (cuts13695.take 2).map (fun c => (1798963201-1+2*2^9*c.k,95071825681744+c.lower,95072202897347+c.upper)) = pointBounds13695 := by
 decide +kernel
def cuts13696 : List PrefixCut := [⟨27,205891453,205891596⟩,
⟨82,617195302,617195733⟩,
⟨128,965753214,965753892⟩]
theorem checked13696 : checkPrefixCuts (2^48) 1799094273 9 Manual.Count131072.C013696.packed 128 cuts13696 = true := by
 decide +kernel
def pointBounds13696 : List (Nat × Nat × Nat) := [(1799121920,95072988634791,95073365851201),(1799178240,95073399938640,95073777155338)]
theorem point_links_checked13696 : (cuts13696.take 2).map (fun c => (1799094273-1+2*2^9*c.k,95072782743338+c.lower,95073159959605+c.upper)) = pointBounds13696 := by
 decide +kernel
def cuts13697 : List PrefixCut := [⟨9,69616625,69616673⟩,
⟨64,472290692,472291028⟩,
⟨119,885276727,885277354⟩,
⟨128,956296522,956297199⟩]
theorem checked13697 : checkPrefixCuts (2^48) 1799225345 9 Manual.Count131072.C013697.packed 128 cuts13697 = true := by
 decide +kernel
def pointBounds13697 : List (Nat × Nat × Nat) := [(1799234560,95073818113177,95074195330170),(1799290880,95074220787244,95074598004525),(1799347200,95074633773279,95075010990851)]
theorem point_links_checked13697 : (cuts13697.take 3).map (fun c => (1799225345-1+2*2^9*c.k,95073748496552+c.lower,95074125713497+c.upper)) = pointBounds13697 := by
 decide +kernel
def cuts13698 : List PrefixCut := [⟨46,345394882,345395118⟩,
⟨101,760075780,760076308⟩,
⟨128,960607079,960607745⟩]
theorem checked13698 : checkPrefixCuts (2^48) 1799356417 9 Manual.Count131072.C013698.packed 128 cuts13698 = true := by
 decide +kernel
def pointBounds13698 : List (Nat × Nat × Nat) := [(1799403520,95075050187956,95075427405814),(1799459840,95075464868854,95075842087004)]
theorem point_links_checked13698 : (cuts13698.take 2).map (fun c => (1799356417-1+2*2^9*c.k,95074704793074+c.lower,95075082010696+c.upper)) = pointBounds13698 := by
 decide +kernel
def cuts13699 : List PrefixCut := [⟨28,211477459,211477610⟩,
⟨83,623316837,623317280⟩,
⟨128,959598514,959599195⟩]
theorem checked13699 : checkPrefixCuts (2^48) 1799487489 9 Manual.Count131072.C013699.packed 128 cuts13699 = true := by
 decide +kernel
def pointBounds13699 : List (Nat × Nat × Nat) := [(1799516160,95075876877612,95076254096051),(1799572480,95076288716990,95076665935721)]
theorem point_links_checked13699 : (cuts13699.take 2).map (fun c => (1799487489-1+2*2^9*c.k,95075665400153+c.lower,95076042618441+c.upper)) = pointBounds13699 := by
 decide +kernel
def cuts13700 : List PrefixCut := [⟨10,77891007,77891060⟩,
⟨65,496586463,496586812⟩,
⟨120,902600444,902601081⟩,
⟨128,961718525,961719204⟩]
theorem checked13700 : checkPrefixCuts (2^48) 1799618561 9 Manual.Count131072.C013700.packed 128 cuts13700 = true := by
 decide +kernel
def pointBounds13700 : List (Nat × Nat × Nat) := [(1799628800,95076702889674,95077080108696),(1799685120,95077121585130,95077498804448),(1799741440,95077527599111,95077904818717)]
theorem point_links_checked13700 : (cuts13700.take 3).map (fun c => (1799618561-1+2*2^9*c.k,95076624998667+c.lower,95077002217636+c.upper)) = pointBounds13700 := by
 decide +kernel
def cuts13701 : List PrefixCut := [⟨47,350167458,350167701⟩,
⟨102,765383069,765383602⟩,
⟨128,953359614,953360283⟩]
theorem checked13701 : checkPrefixCuts (2^48) 1799749633 9 Manual.Count131072.C013701.packed 128 cuts13701 = true := by
 decide +kernel
def pointBounds13701 : List (Nat × Nat × Nat) := [(1799797760,95077936884650,95078314104541),(1799854080,95078352100261,95078729320442)]
theorem point_links_checked13701 : (cuts13701.take 2).map (fun c => (1799749633-1+2*2^9*c.k,95077586717192+c.lower,95077963936840+c.upper)) = pointBounds13701 := by
 decide +kernel
def cuts13702 : List PrefixCut := [⟨29,217217349,217217504⟩,
⟨84,640226105,640226553⟩,
⟨128,972993957,972994637⟩]
theorem checked13702 : checkPrefixCuts (2^48) 1799880705 9 Manual.Count131072.C013702.packed 128 cuts13702 = true := by
 decide +kernel
def pointBounds13702 : List (Nat × Nat × Nat) := [(1799910400,95078757294155,95079134514627),(1799966720,95079180302911,95079557523676)]
theorem point_links_checked13702 : (cuts13702.take 2).map (fun c => (1799880705-1+2*2^9*c.k,95078540076806+c.lower,95078917297123+c.upper)) = pointBounds13702 := by
 decide +kernel
def cuts13703 : List PrefixCut := [⟨11,84441645,84441706⟩,
⟨66,500230821,500231178⟩,
⟨121,910221409,910222053⟩,
⟨128,964322944,964323626⟩]
theorem checked13703 : checkPrefixCuts (2^48) 1800011777 9 Manual.Count131072.C013703.packed 128 cuts13703 = true := by
 decide +kernel
def pointBounds13703 : List (Nat × Nat × Nat) := [(1800023040,95079597512408,95079974733466),(1800079360,95080013301584,95080390522938),(1800135680,95080423292172,95080800513813)]
theorem point_links_checked13703 : (cuts13703.take 3).map (fun c => (1800011777-1+2*2^9*c.k,95079513070763+c.lower,95079890291760+c.upper)) = pointBounds13703 := by
 decide +kernel
def cuts13704 : List PrefixCut := [⟨48,352436304,352436551⟩,
⟨103,771469920,771470461⟩,
⟨128,958779900,958780573⟩]
theorem checked13704 : checkPrefixCuts (2^48) 1800142849 9 Manual.Count131072.C013704.packed 128 cuts13704 = true := by
 decide +kernel
def pointBounds13704 : List (Nat × Nat × Nat) := [(1800192000,95080829830011,95081207051937),(1800248320,95081248863627,95081626085847)]
theorem point_links_checked13704 : (cuts13704.take 2).map (fun c => (1800142849-1+2*2^9*c.k,95080477393707+c.lower,95080854615386+c.upper)) = pointBounds13704 := by
 decide +kernel
def cuts13705 : List PrefixCut := [⟨30,221391335,221391487⟩,
⟨85,631017773,631018214⟩,
⟨128,964338205,964338879⟩]
theorem checked13705 : checkPrefixCuts (2^48) 1800273921 9 Manual.Count131072.C013705.packed 128 cuts13705 = true := by
 decide +kernel
def pointBounds13705 : List (Nat × Nat × Nat) := [(1800304640,95081657564942,95082034787446),(1800360960,95082067191380,95082444414173)]
theorem point_links_checked13705 : (cuts13705.take 2).map (fun c => (1800273921-1+2*2^9*c.k,95081436173607+c.lower,95081813395959+c.upper)) = pointBounds13705 := by
 decide +kernel
def cuts13706 : List PrefixCut := [⟨12,91145769,91145832⟩,
⟨67,506531133,506531485⟩,
⟨122,918777000,918777648⟩,
⟨128,965206604,965207284⟩]
theorem checked13706 : checkPrefixCuts (2^48) 1800404993 9 Manual.Count131072.C013706.packed 128 cuts13706 = true := by
 decide +kernel
def pointBounds13706 : List (Nat × Nat × Nat) := [(1800417280,95082491657581,95082868880670),(1800473600,95082907042945,95083284266323),(1800529920,95083319288812,95083696512486)]
theorem point_links_checked13706 : (cuts13706.take 3).map (fun c => (1800404993-1+2*2^9*c.k,95082400511812+c.lower,95082777734838+c.upper)) = pointBounds13706 := by
 decide +kernel
def cuts13707 : List PrefixCut := [⟨49,362833195,362833454⟩,
⟨104,783338262,783338814⟩,
⟨128,966699332,966700013⟩]
theorem checked13707 : checkPrefixCuts (2^48) 1800536065 9 Manual.Count131072.C013707.packed 128 cuts13707 = true := by
 decide +kernel
def pointBounds13707 : List (Nat × Nat × Nat) := [(1800586240,95083728551611,95084105775576),(1800642560,95084149056678,95084526280936)]
theorem point_links_checked13707 : (cuts13707.take 2).map (fun c => (1800536065-1+2*2^9*c.k,95083365718416+c.lower,95083742942122+c.upper)) = pointBounds13707 := by
 decide +kernel
def cuts13708 : List PrefixCut := [⟨31,236349205,236349370⟩,
⟨86,641509429,641509881⟩,
⟨128,953811775,953812448⟩]
theorem checked13708 : checkPrefixCuts (2^48) 1800667137 9 Manual.Count131072.C013708.packed 128 cuts13708 = true := by
 decide +kernel
def pointBounds13708 : List (Nat × Nat × Nat) := [(1800698880,95084568766953,95084945991505),(1800755200,95084973927177,95085351152016)]
theorem point_links_checked13708 : (cuts13708.take 2).map (fun c => (1800667137-1+2*2^9*c.k,95084332417748+c.lower,95084709642135+c.upper)) = pointBounds13708 := by
 decide +kernel
def cuts13709 : List PrefixCut := [⟨13,95502378,95502446⟩,
⟨68,507514596,507514953⟩,
⟨123,925921977,925922631⟩,
⟨128,962025996,962026676⟩]
theorem checked13709 : checkPrefixCuts (2^48) 1800798209 9 Manual.Count131072.C013709.packed 128 cuts13709 = true := by
 decide +kernel
def pointBounds13709 : List (Nat × Nat × Nat) := [(1800811520,95085381731901,95085758957029),(1800867840,95085793744119,95086170969536),(1800924160,95086212151500,95086589377214)]
theorem point_links_checked13709 : (cuts13709.take 3).map (fun c => (1800798209-1+2*2^9*c.k,95085286229523+c.lower,95085663454583+c.upper)) = pointBounds13709 := by
 decide +kernel
def cuts13710 : List PrefixCut := [⟨50,376976337,376976601⟩,
⟨105,784104937,784105489⟩,
⟨128,953985525,953986196⟩]
theorem checked13710 : checkPrefixCuts (2^48) 1800929281 9 Manual.Count131072.C013710.packed 128 cuts13710 = true := by
 decide +kernel
def pointBounds13710 : List (Nat × Nat × Nat) := [(1800980480,95086625231856,95087002457860),(1801036800,95087032360456,95087409586748)]
theorem point_links_checked13710 : (cuts13710.take 2).map (fun c => (1800929281-1+2*2^9*c.k,95086248255519+c.lower,95086625481259+c.upper)) = pointBounds13710 := by
 decide +kernel
def cuts13711 : List PrefixCut := [⟨32,235516083,235516251⟩,
⟨87,648401479,648401937⟩,
⟨128,957510089,957510763⟩]
theorem checked13711 : checkPrefixCuts (2^48) 1801060353 9 Manual.Count131072.C013711.packed 128 cuts13711 = true := by
 decide +kernel
def pointBounds13711 : List (Nat × Nat × Nat) := [(1801093120,95087437757127,95087814983706),(1801149440,95087850642523,95088227869392)]
theorem point_links_checked13711 : (cuts13711.take 2).map (fun c => (1801060353-1+2*2^9*c.k,95087202241044+c.lower,95087579467455+c.upper)) = pointBounds13711 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000115
