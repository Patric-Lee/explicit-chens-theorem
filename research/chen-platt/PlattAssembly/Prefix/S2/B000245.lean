import PlattAssemblyKernel
import PlattCertificates.Count131072.C017840
import PlattCertificates.Count131072.C017841
import PlattCertificates.Count131072.C017842
import PlattCertificates.Count131072.C017843
import PlattCertificates.Count131072.C017844
import PlattCertificates.Count131072.C017845
import PlattCertificates.Count131072.C017846
import PlattCertificates.Count131072.C017847
import PlattCertificates.Count131072.C017848
import PlattCertificates.Count131072.C017849
import PlattCertificates.Count131072.C017850
import PlattCertificates.Count131072.C017851
import PlattCertificates.Count131072.C017852
import PlattCertificates.Count131072.C017853
import PlattCertificates.Count131072.C017854
import PlattCertificates.Count131072.C017855
import PlattCertificates.Count131072.C017856
import PlattCertificates.Count131072.C017857
import PlattCertificates.Count131072.C017858
import PlattCertificates.Count131072.C017859
import PlattCertificates.Count131072.C017860
import PlattCertificates.Count131072.C017861
import PlattCertificates.Count131072.C017862
import PlattCertificates.Count131072.C017863
import PlattCertificates.Count131072.C017864
import PlattCertificates.Count131072.C017865
import PlattCertificates.Count131072.C017866
import PlattCertificates.Count131072.C017867
import PlattCertificates.Count131072.C017868
import PlattCertificates.Count131072.C017869
import PlattCertificates.Count131072.C017870
import PlattCertificates.Count131072.C017871
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000245
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17840 : List PrefixCut := [⟨12,67416606,67416648⟩,
⟨84,474552538,474552825⟩,
⟨128,727503993,727504435⟩]
theorem checked17840 : checkPrefixCuts (2^48) 2342256641 9 Manual.Count131072.C017840.packed 128 cuts17840 = true := by
 decide +kernel
def pointBounds17840 : List (Nat × Nat × Nat) := [(2342268928,98536081570156,98536461049598),(2342342656,98536488706088,98536868185775)]
theorem point_links_checked17840 : (cuts17840.take 2).map (fun c => (2342256641-1+2*2^9*c.k,98536014153550+c.lower,98536393632950+c.upper)) = pointBounds17840 := by
 decide +kernel
def cuts17841 : List PrefixCut := [⟨28,162583316,162583416⟩,
⟨100,571976755,571977108⟩,
⟨128,734552985,734553438⟩]
theorem checked17841 : checkPrefixCuts (2^48) 2342387713 9 Manual.Count131072.C017841.packed 128 cuts17841 = true := by
 decide +kernel
def pointBounds17841 : List (Nat × Nat × Nat) := [(2342416384,98536904240859,98537283720801),(2342490112,98537313634298,98537693114493)]
theorem point_links_checked17841 : (cuts17841.take 2).map (fun c => (2342387713-1+2*2^9*c.k,98536741657543+c.lower,98537121137385+c.upper)) = pointBounds17841 := by
 decide +kernel
def cuts17842 : List PrefixCut := [⟨44,255335580,255335736⟩,
⟨116,663501638,663502043⟩,
⟨128,730426674,730427120⟩]
theorem checked17842 : checkPrefixCuts (2^48) 2342518785 9 Manual.Count131072.C017842.packed 128 cuts17842 = true := by
 decide +kernel
def pointBounds17842 : List (Nat × Nat × Nat) := [(2342563840,98537731546108,98538111026559),(2342637568,98538139712166,98538519192866)]
theorem point_links_checked17842 : (cuts17842.take 2).map (fun c => (2342518785-1+2*2^9*c.k,98537476210528+c.lower,98537855690823+c.upper)) = pointBounds17842 := by
 decide +kernel
def cuts17843 : List PrefixCut := [⟨60,350119414,350119627⟩,
⟨128,745404441,745404897⟩]
theorem checked17843 : checkPrefixCuts (2^48) 2342649857 9 Manual.Count131072.C017843.packed 128 cuts17843 = true := by
 decide +kernel
def pointBounds17843 : List (Nat × Nat × Nat) := [(2342711296,98538556756616,98538936237570)]
theorem point_links_checked17843 : (cuts17843.take 1).map (fun c => (2342649857-1+2*2^9*c.k,98538206637202+c.lower,98538586117943+c.upper)) = pointBounds17843 := by
 decide +kernel
def cuts17844 : List PrefixCut := [⟨4,22707504,22707516⟩,
⟨76,428672430,428672696⟩,
⟨128,731666201,731666649⟩]
theorem checked17844 : checkPrefixCuts (2^48) 2342780929 9 Manual.Count131072.C017844.packed 128 cuts17844 = true := by
 decide +kernel
def pointBounds17844 : List (Nat × Nat × Nat) := [(2342785024,98538974749147,98539354230356),(2342858752,98539380714073,98539760195536)]
theorem point_links_checked17844 : (cuts17844.take 2).map (fun c => (2342780929-1+2*2^9*c.k,98538952041643+c.lower,98539331522840+c.upper)) = pointBounds17844 := by
 decide +kernel
def cuts17845 : List PrefixCut := [⟨20,115452991,115453064⟩,
⟨92,518148763,518149087⟩,
⟨128,721654295,721654740⟩]
theorem checked17845 : checkPrefixCuts (2^48) 2342912001 9 Manual.Count131072.C017845.packed 128 cuts17845 = true := by
 decide +kernel
def pointBounds17845 : List (Nat × Nat × Nat) := [(2342932480,98539799160835,98540178642553),(2343006208,98540201856607,98540581338576)]
theorem point_links_checked17845 : (cuts17845.take 2).map (fun c => (2342912001-1+2*2^9*c.k,98539683707844+c.lower,98540063189489+c.upper)) = pointBounds17845 := by
 decide +kernel
def cuts17846 : List PrefixCut := [⟨36,203502322,203502445⟩,
⟨108,613981056,613981428⟩,
⟨128,730022769,730023212⟩]
theorem checked17846 : checkPrefixCuts (2^48) 2343043073 9 Manual.Count131072.C017846.packed 128 cuts17846 = true := by
 decide +kernel
def pointBounds17846 : List (Nat × Nat × Nat) := [(2343079936,98540608864461,98540988346674),(2343153664,98541019343195,98541398825657)]
theorem point_links_checked17846 : (cuts17846.take 2).map (fun c => (2343043073-1+2*2^9*c.k,98540405362139+c.lower,98540784844229+c.upper)) = pointBounds17846 := by
 decide +kernel
def cuts17847 : List PrefixCut := [⟨52,295385135,295385322⟩,
⟨124,704516773,704517215⟩,
⟨128,728900901,728901357⟩]
theorem checked17847 : checkPrefixCuts (2^48) 2343174145 9 Manual.Count131072.C017847.packed 128 cuts17847 = true := by
 decide +kernel
def pointBounds17847 : List (Nat × Nat × Nat) := [(2343227392,98541430770043,98541810252763),(2343301120,98541839901681,98542219384656)]
theorem point_links_checked17847 : (cuts17847.take 2).map (fun c => (2343174145-1+2*2^9*c.k,98541135384908+c.lower,98541514867441+c.upper)) = pointBounds17847 := by
 decide +kernel
def cuts17848 : List PrefixCut := [⟨68,385815685,385815924⟩,
⟨128,727298673,727299122⟩]
theorem checked17848 : checkPrefixCuts (2^48) 2343305217 9 Manual.Count131072.C017848.packed 128 cuts17848 = true := by
 decide +kernel
def pointBounds17848 : List (Nat × Nat × Nat) := [(2343374848,98542250101494,98542629584722)]
theorem point_links_checked17848 : (cuts17848.take 1).map (fun c => (2343305217-1+2*2^9*c.k,98541864285809+c.lower,98542243768798+c.upper)) = pointBounds17848 := by
 decide +kernel
def cuts17849 : List PrefixCut := [⟨12,69664794,69664837⟩,
⟨84,482000847,482001148⟩,
⟨128,733623942,733624399⟩]
theorem checked17849 : checkPrefixCuts (2^48) 2343436289 9 Manual.Count131072.C017849.packed 128 cuts17849 = true := by
 decide +kernel
def pointBounds17849 : List (Nat × Nat × Nat) := [(2343448576,98542661249276,98543040732757),(2343522304,98543073585329,98543453069068)]
theorem point_links_checked17849 : (cuts17849.take 2).map (fun c => (2343436289-1+2*2^9*c.k,98542591584482+c.lower,98542971067920+c.upper)) = pointBounds17849 := by
 decide +kernel
def cuts17850 : List PrefixCut := [⟨28,161660758,161660858⟩,
⟨100,567725489,567725841⟩,
⟨128,726136498,726136943⟩]
theorem checked17850 : checkPrefixCuts (2^48) 2343567361 9 Manual.Count131072.C017850.packed 128 cuts17850 = true := by
 decide +kernel
def pointBounds17850 : List (Nat × Nat × Nat) := [(2343596032,98543486869182,98543866353177),(2343669760,98543892933913,98544272418160)]
theorem point_links_checked17850 : (cuts17850.take 2).map (fun c => (2343567361-1+2*2^9*c.k,98543325208424+c.lower,98543704692319+c.upper)) = pointBounds17850 := by
 decide +kernel
def cuts17851 : List PrefixCut := [⟨44,252204668,252204822⟩,
⟨116,655962043,655962447⟩,
⟨128,722373027,722373474⟩]
theorem checked17851 : checkPrefixCuts (2^48) 2343698433 9 Manual.Count131072.C017851.packed 128 cuts17851 = true := by
 decide +kernel
def pointBounds17851 : List (Nat × Nat × Nat) := [(2343743488,98544303549590,98544683034084),(2343817216,98544707306965,98545086791709)]
theorem point_links_checked17851 : (cuts17851.take 2).map (fun c => (2343698433-1+2*2^9*c.k,98544051344922+c.lower,98544430829262+c.upper)) = pointBounds17851 := by
 decide +kernel
def cuts17852 : List PrefixCut := [⟨60,345139555,345139761⟩,
⟨128,727616504,727616940⟩]
theorem checked17852 : checkPrefixCuts (2^48) 2343829505 9 Manual.Count131072.C017852.packed 128 cuts17852 = true := by
 decide +kernel
def pointBounds17852 : List (Nat × Nat × Nat) := [(2343890944,98545118857504,98545498342497)]
theorem point_links_checked17852 : (cuts17852.take 1).map (fun c => (2343829505-1+2*2^9*c.k,98544773717949+c.lower,98545153202736+c.upper)) = pointBounds17852 := by
 decide +kernel
def cuts17853 : List PrefixCut := [⟨4,20054202,20054215⟩,
⟨76,427135821,427136082⟩,
⟨128,720610869,720611312⟩]
theorem checked17853 : checkPrefixCuts (2^48) 2343960577 9 Manual.Count131072.C017853.packed 128 cuts17853 = true := by
 decide +kernel
def pointBounds17853 : List (Nat × Nat × Nat) := [(2343964672,98545521388655,98545900873891),(2344038400,98545928470274,98546307955758)]
theorem point_links_checked17853 : (cuts17853.take 2).map (fun c => (2343960577-1+2*2^9*c.k,98545501334453+c.lower,98545880819676+c.upper)) = pointBounds17853 := by
 decide +kernel
def cuts17854 : List PrefixCut := [⟨20,113593711,113593780⟩,
⟨92,525332612,525332931⟩,
⟨128,730056534,730056980⟩]
theorem checked17854 : checkPrefixCuts (2^48) 2344091649 9 Manual.Count131072.C017854.packed 128 cuts17854 = true := by
 decide +kernel
def pointBounds17854 : List (Nat × Nat × Nat) := [(2344112128,98546335539033,98546715024768),(2344185856,98546747277934,98547126763919)]
theorem point_links_checked17854 : (cuts17854.take 2).map (fun c => (2344091649-1+2*2^9*c.k,98546221945322+c.lower,98546601430988+c.upper)) = pointBounds17854 := by
 decide +kernel
def cuts17855 : List PrefixCut := [⟨36,206401658,206401783⟩,
⟨108,613912270,613912647⟩,
⟨128,727374220,727374664⟩]
theorem checked17855 : checkPrefixCuts (2^48) 2344222721 9 Manual.Count131072.C017855.packed 128 cuts17855 = true := by
 decide +kernel
def pointBounds17855 : List (Nat × Nat × Nat) := [(2344259584,98547158403514,98547537889751),(2344333312,98547565914126,98547945400615)]
theorem point_links_checked17855 : (cuts17855.take 2).map (fun c => (2344222721-1+2*2^9*c.k,98546952001856+c.lower,98547331487968+c.upper)) = pointBounds17855 := by
 decide +kernel
def cuts17856 : List PrefixCut := [⟨52,299678934,299679115⟩,
⟨124,712926867,712927303⟩,
⟨128,733216739,733217188⟩]
theorem checked17856 : checkPrefixCuts (2^48) 2344353793 9 Manual.Count131072.C017856.packed 128 cuts17856 = true := by
 decide +kernel
def pointBounds17856 : List (Nat × Nat × Nat) := [(2344407040,98547979055010,98548358541747),(2344480768,98548392302943,98548771789935)]
theorem point_links_checked17856 : (cuts17856.take 2).map (fun c => (2344353793-1+2*2^9*c.k,98547679376076+c.lower,98548058862632+c.upper)) = pointBounds17856 := by
 decide +kernel
def cuts17857 : List PrefixCut := [⟨68,384781246,384781479⟩,
⟨128,727052803,727053244⟩]
theorem checked17857 : checkPrefixCuts (2^48) 2344484865 9 Manual.Count131072.C017857.packed 128 cuts17857 = true := by
 decide +kernel
def pointBounds17857 : List (Nat × Nat × Nat) := [(2344554496,98548797374061,98549176861299)]
theorem point_links_checked17857 : (cuts17857.take 1).map (fun c => (2344484865-1+2*2^9*c.k,98548412592815+c.lower,98548792079820+c.upper)) = pointBounds17857 := by
 decide +kernel
def cuts17858 : List PrefixCut := [⟨12,69629738,69629781⟩,
⟨84,476716084,476716382⟩,
⟨128,724851280,724851731⟩]
theorem checked17858 : checkPrefixCuts (2^48) 2344615937 9 Manual.Count131072.C017858.packed 128 cuts17858 = true := by
 decide +kernel
def pointBounds17858 : List (Nat × Nat × Nat) := [(2344628224,98549209275356,98549588762845),(2344701952,98549616361702,98549995849446)]
theorem point_links_checked17858 : (cuts17858.take 2).map (fun c => (2344615937-1+2*2^9*c.k,98549139645618+c.lower,98549519133064+c.upper)) = pointBounds17858 := by
 decide +kernel
def cuts17859 : List PrefixCut := [⟨28,161939563,161939665⟩,
⟨100,574522388,574522741⟩,
⟨128,731173181,731173631⟩]
theorem checked17859 : checkPrefixCuts (2^48) 2344747009 9 Manual.Count131072.C017859.packed 128 cuts17859 = true := by
 decide +kernel
def pointBounds17859 : List (Nat × Nat × Nat) := [(2344775680,98550026436461,98550405924460),(2344849408,98550439019286,98550818507536)]
theorem point_links_checked17859 : (cuts17859.take 2).map (fun c => (2344747009-1+2*2^9*c.k,98549864496898+c.lower,98550243984795+c.upper)) = pointBounds17859 := by
 decide +kernel
def cuts17860 : List PrefixCut := [⟨44,243555125,243555276⟩,
⟨116,656111945,656112343⟩,
⟨128,726210500,726210939⟩]
theorem checked17860 : checkPrefixCuts (2^48) 2344878081 9 Manual.Count131072.C017860.packed 128 cuts17860 = true := by
 decide +kernel
def pointBounds17860 : List (Nat × Nat × Nat) := [(2344923136,98550839225204,98551218713702),(2344996864,98551251782024,98551631270769)]
theorem point_links_checked17860 : (cuts17860.take 2).map (fun c => (2344878081-1+2*2^9*c.k,98550595670079+c.lower,98550975158426+c.upper)) = pointBounds17860 := by
 decide +kernel
def cuts17861 : List PrefixCut := [⟨60,330922375,330922577⟩,
⟨128,724369353,724369801⟩]
theorem checked17861 : checkPrefixCuts (2^48) 2345009153 9 Manual.Count131072.C017861.packed 128 cuts17861 = true := by
 decide +kernel
def pointBounds17861 : List (Nat × Nat × Nat) := [(2345070592,98551652802954,98552032291942)]
theorem point_links_checked17861 : (cuts17861.take 1).map (fun c => (2345009153-1+2*2^9*c.k,98551321880579+c.lower,98551701369365+c.upper)) = pointBounds17861 := by
 decide +kernel
def cuts17862 : List PrefixCut := [⟨4,23524832,23524846⟩,
⟨76,435082479,435082749⟩,
⟨128,734650960,734651411⟩]
theorem checked17862 : checkPrefixCuts (2^48) 2345140225 9 Manual.Count131072.C017862.packed 128 cuts17862 = true := by
 decide +kernel
def pointBounds17862 : List (Nat × Nat × Nat) := [(2345144320,98552069774764,98552449264012),(2345218048,98552481332411,98552860821915)]
theorem point_links_checked17862 : (cuts17862.take 2).map (fun c => (2345140225-1+2*2^9*c.k,98552046249932+c.lower,98552425739166+c.upper)) = pointBounds17862 := by
 decide +kernel
def cuts17863 : List PrefixCut := [⟨20,115216811,115216883⟩,
⟨92,526868709,526869030⟩,
⟨128,734369960,734370411⟩]
theorem checked17863 : checkPrefixCuts (2^48) 2345271297 9 Manual.Count131072.C017863.packed 128 cuts17863 = true := by
 decide +kernel
def pointBounds17863 : List (Nat × Nat × Nat) := [(2345291776,98552896117703,98553275607460),(2345365504,98553307769601,98553687259607)]
theorem point_links_checked17863 : (cuts17863.take 2).map (fun c => (2345271297-1+2*2^9*c.k,98552780900892+c.lower,98553160390577+c.upper)) = pointBounds17863 := by
 decide +kernel
def cuts17864 : List PrefixCut := [⟨36,206537857,206537984⟩,
⟨108,612283443,612283815⟩,
⟨128,723528219,723528660⟩]
theorem checked17864 : checkPrefixCuts (2^48) 2345402369 9 Manual.Count131072.C017864.packed 128 cuts17864 = true := by
 decide +kernel
def pointBounds17864 : List (Nat × Nat × Nat) := [(2345439232,98553721808709,98554101298972),(2345512960,98554127554295,98554507044803)]
theorem point_links_checked17864 : (cuts17864.take 2).map (fun c => (2345402369-1+2*2^9*c.k,98553515270852+c.lower,98553894760988+c.upper)) = pointBounds17864 := by
 decide +kernel
def cuts17865 : List PrefixCut := [⟨52,295088095,295088275⟩,
⟨124,699728172,699728597⟩,
⟨128,723487783,723488223⟩]
theorem checked17865 : checkPrefixCuts (2^48) 2345533441 9 Manual.Count131072.C017865.packed 128 cuts17865 = true := by
 decide +kernel
def pointBounds17865 : List (Nat × Nat × Nat) := [(2345586688,98554533887166,98554913377923),(2345660416,98554938527243,98555318018245)]
theorem point_links_checked17865 : (cuts17865.take 2).map (fun c => (2345533441-1+2*2^9*c.k,98554238799071+c.lower,98554618289648+c.upper)) = pointBounds17865 := by
 decide +kernel
def cuts17866 : List PrefixCut := [⟨68,390467442,390467686⟩,
⟨128,730887029,730887481⟩]
theorem checked17866 : checkPrefixCuts (2^48) 2345664513 9 Manual.Count131072.C017866.packed 128 cuts17866 = true := by
 decide +kernel
def pointBounds17866 : List (Nat × Nat × Nat) := [(2345734144,98555352754296,98555732245557)]
theorem point_links_checked17866 : (cuts17866.take 1).map (fun c => (2345664513-1+2*2^9*c.k,98554962286854+c.lower,98555341777871+c.upper)) = pointBounds17866 := by
 decide +kernel
def cuts17867 : List PrefixCut := [⟨12,73674425,73674469⟩,
⟨84,486915453,486915749⟩,
⟨128,737325552,737326004⟩]
theorem checked17867 : checkPrefixCuts (2^48) 2345795585 9 Manual.Count131072.C017867.packed 128 cuts17867 = true := by
 decide +kernel
def pointBounds17867 : List (Nat × Nat × Nat) := [(2345807872,98555766848308,98556146339821),(2345881600,98556180089336,98556559581101)]
theorem point_links_checked17867 : (cuts17867.take 2).map (fun c => (2345795585-1+2*2^9*c.k,98555693173883+c.lower,98556072665352+c.upper)) = pointBounds17867 := by
 decide +kernel
def cuts17868 : List PrefixCut := [⟨28,156578841,156578937⟩,
⟨100,561995256,561995603⟩,
⟨128,721806679,721807124⟩]
theorem checked17868 : checkPrefixCuts (2^48) 2345926657 9 Manual.Count131072.C017868.packed 128 cuts17868 = true := by
 decide +kernel
def pointBounds17868 : List (Nat × Nat × Nat) := [(2345955328,98556587078276,98556966570293),(2346029056,98556992494691,98557371986959)]
theorem point_links_checked17868 : (cuts17868.take 2).map (fun c => (2345926657-1+2*2^9*c.k,98556430499435+c.lower,98556809991356+c.upper)) = pointBounds17868 := by
 decide +kernel
def cuts17869 : List PrefixCut := [⟨44,255310345,255310500⟩,
⟨116,666220046,666220447⟩,
⟨128,735563525,735563971⟩]
theorem checked17869 : checkPrefixCuts (2^48) 2346057729 9 Manual.Count131072.C017869.packed 128 cuts17869 = true := by
 decide +kernel
def pointBounds17869 : List (Nat × Nat × Nat) := [(2346102784,98557407616459,98557787108980),(2346176512,98557818526160,98558198018927)]
theorem point_links_checked17869 : (cuts17869.take 2).map (fun c => (2346057729-1+2*2^9*c.k,98557152306114+c.lower,98557531798480+c.upper)) = pointBounds17869 := by
 decide +kernel
def cuts17870 : List PrefixCut := [⟨60,333035522,333035727⟩,
⟨128,724845085,724845528⟩]
theorem checked17870 : checkPrefixCuts (2^48) 2346188801 9 Manual.Count131072.C017870.packed 128 cuts17870 = true := by
 decide +kernel
def pointBounds17870 : List (Nat × Nat × Nat) := [(2346250240,98558220905161,98558600398178)]
theorem point_links_checked17870 : (cuts17870.take 1).map (fun c => (2346188801-1+2*2^9*c.k,98557887869639+c.lower,98558267362451+c.upper)) = pointBounds17870 := by
 decide +kernel
def cuts17871 : List PrefixCut := [⟨4,21833505,21833517⟩,
⟨76,435223599,435223865⟩,
⟨128,719766527,719766972⟩]
theorem checked17871 : checkPrefixCuts (2^48) 2346319873 9 Manual.Count131072.C017871.packed 128 cuts17871 = true := by
 decide +kernel
def pointBounds17871 : List (Nat × Nat × Nat) := [(2346323968,98558634548229,98559014041496),(2346397696,98559047938323,98559427431844)]
theorem point_links_checked17871 : (cuts17871.take 2).map (fun c => (2346319873-1+2*2^9*c.k,98558612714724+c.lower,98558992207979+c.upper)) = pointBounds17871 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000245
