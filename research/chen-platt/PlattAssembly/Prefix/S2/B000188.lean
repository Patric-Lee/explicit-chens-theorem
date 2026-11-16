import PlattAssemblyKernel
import PlattCertificates.Count131072.C016016
import PlattCertificates.Count131072.C016017
import PlattCertificates.Count131072.C016018
import PlattCertificates.Count131072.C016019
import PlattCertificates.Count131072.C016020
import PlattCertificates.Count131072.C016021
import PlattCertificates.Count131072.C016022
import PlattCertificates.Count131072.C016023
import PlattCertificates.Count131072.C016024
import PlattCertificates.Count131072.C016025
import PlattCertificates.Count131072.C016026
import PlattCertificates.Count131072.C016027
import PlattCertificates.Count131072.C016028
import PlattCertificates.Count131072.C016029
import PlattCertificates.Count131072.C016030
import PlattCertificates.Count131072.C016031
import PlattCertificates.Count131072.C016032
import PlattCertificates.Count131072.C016033
import PlattCertificates.Count131072.C016034
import PlattCertificates.Count131072.C016035
import PlattCertificates.Count131072.C016036
import PlattCertificates.Count131072.C016037
import PlattCertificates.Count131072.C016038
import PlattCertificates.Count131072.C016039
import PlattCertificates.Count131072.C016040
import PlattCertificates.Count131072.C016041
import PlattCertificates.Count131072.C016042
import PlattCertificates.Count131072.C016043
import PlattCertificates.Count131072.C016044
import PlattCertificates.Count131072.C016045
import PlattCertificates.Count131072.C016046
import PlattCertificates.Count131072.C016047
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000188
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16016 : List PrefixCut := [⟨65,412332675,412332943⟩,
⟨128,812474263,812474792⟩]
theorem checked16016 : checkPrefixCuts (2^48) 2103181313 9 Manual.Count131072.C016016.packed 128 cuts16016 = true := by
 decide +kernel
def pointBounds16016 : List (Nat × Nat × Nat) := [(2103247872,97128238405659,97128617002278)]
theorem point_links_checked16016 : (cuts16016.take 1).map (fun c => (2103181313-1+2*2^9*c.k,97127826072984+c.lower,97128204669335+c.upper)) = pointBounds16016 := by
 decide +kernel
def cuts16017 : List PrefixCut := [⟨2,11375083,11375090⟩,
⟨67,432513969,432514247⟩,
⟨128,818713387,818713916⟩]
theorem checked16017 : checkPrefixCuts (2^48) 2103312385 9 Manual.Count131072.C016017.packed 128 cuts16017 = true := by
 decide +kernel
def pointBounds16017 : List (Nat × Nat × Nat) := [(2103314432,97128649922330,97129028519217),(2103380992,97129071061216,97129449658374)]
theorem point_links_checked16017 : (cuts16017.take 2).map (fun c => (2103312385-1+2*2^9*c.k,97128638547247+c.lower,97129017144127+c.upper)) = pointBounds16017 := by
 decide +kernel
def cuts16018 : List PrefixCut := [⟨4,24086898,24086914⟩,
⟨69,440917019,440917303⟩,
⟨128,817993052,817993578⟩]
theorem checked16018 : checkPrefixCuts (2^48) 2103443457 9 Manual.Count131072.C016018.packed 128 cuts16018 = true := by
 decide +kernel
def pointBounds16018 : List (Nat × Nat × Nat) := [(2103447552,97129481347532,97129859944957),(2103514112,97129898177653,97130276775346)]
theorem point_links_checked16018 : (cuts16018.take 2).map (fun c => (2103443457-1+2*2^9*c.k,97129457260634+c.lower,97129835858043+c.upper)) = pointBounds16018 := by
 decide +kernel
def cuts16019 : List PrefixCut := [⟨6,36797118,36797142⟩,
⟨71,456544622,456544923⟩,
⟨128,817540806,817541340⟩]
theorem checked16019 : checkPrefixCuts (2^48) 2103574529 9 Manual.Count131072.C016019.packed 128 cuts16019 = true := by
 decide +kernel
def pointBounds16019 : List (Nat × Nat × Nat) := [(2103580672,97130312050804,97130690648763),(2103647232,97130731798308,97131110396544)]
theorem point_links_checked16019 : (cuts16019.take 2).map (fun c => (2103574529-1+2*2^9*c.k,97130275253686+c.lower,97130653851621+c.upper)) = pointBounds16019 := by
 decide +kernel
def cuts16020 : List PrefixCut := [⟨8,48435346,48435378⟩,
⟨73,466149306,466149608⟩,
⟨128,820433219,820433748⟩]
theorem checked16020 : checkPrefixCuts (2^48) 2103705601 9 Manual.Count131072.C016020.packed 128 cuts16020 = true := by
 decide +kernel
def pointBounds16020 : List (Nat × Nat × Nat) := [(2103713792,97131141229838,97131519828339),(2103780352,97131558943798,97131937542569)]
theorem point_links_checked16020 : (cuts16020.take 2).map (fun c => (2103705601-1+2*2^9*c.k,97131092794492+c.lower,97131471392961+c.upper)) = pointBounds16020 := by
 decide +kernel
def cuts16021 : List PrefixCut := [⟨10,64487211,64487253⟩,
⟨75,470267630,470267930⟩,
⟨128,801919723,801920234⟩]
theorem checked16021 : checkPrefixCuts (2^48) 2103836673 9 Manual.Count131072.C016021.packed 128 cuts16021 = true := by
 decide +kernel
def pointBounds16021 : List (Nat × Nat × Nat) := [(2103846912,97131977714922,97132356313962),(2103913472,97132383495341,97132762094639)]
theorem point_links_checked16021 : (cuts16021.take 2).map (fun c => (2103836673-1+2*2^9*c.k,97131913227711+c.lower,97132291826709+c.upper)) = pointBounds16021 := by
 decide +kernel
def cuts16022 : List PrefixCut := [⟨12,77326287,77326336⟩,
⟨77,497529199,497529516⟩,
⟨128,823274291,823274814⟩]
theorem checked16022 : checkPrefixCuts (2^48) 2103967745 9 Manual.Count131072.C016022.packed 128 cuts16022 = true := by
 decide +kernel
def pointBounds16022 : List (Nat × Nat × Nat) := [(2103980032,97132792473721,97133171073279),(2104046592,97133212676633,97133591276459)]
theorem point_links_checked16022 : (cuts16022.take 2).map (fun c => (2103967745-1+2*2^9*c.k,97132715147434+c.lower,97133093746943+c.upper)) = pointBounds16022 := by
 decide +kernel
def cuts16023 : List PrefixCut := [⟨14,92705461,92705519⟩,
⟨79,503651649,503651972⟩,
⟨128,813993041,813993563⟩]
theorem checked16023 : checkPrefixCuts (2^48) 2104098817 9 Manual.Count131072.C016023.packed 128 cuts16023 = true := by
 decide +kernel
def pointBounds16023 : List (Nat × Nat × Nat) := [(2104113152,97133631127186,97134009727276),(2104179712,97134042073374,97134420673729)]
theorem point_links_checked16023 : (cuts16023.take 2).map (fun c => (2104098817-1+2*2^9*c.k,97133538421725+c.lower,97133917021757+c.upper)) = pointBounds16023 := by
 decide +kernel
def cuts16024 : List PrefixCut := [⟨16,100324263,100324328⟩,
⟨81,524620781,524621119⟩,
⟨128,822770562,822771094⟩]
theorem checked16024 : checkPrefixCuts (2^48) 2104229889 9 Manual.Count131072.C016024.packed 128 cuts16024 = true := by
 decide +kernel
def pointBounds16024 : List (Nat × Nat × Nat) := [(2104246272,97134452739029,97134831339648),(2104312832,97134877035547,97135255636439)]
theorem point_links_checked16024 : (cuts16024.take 2).map (fun c => (2104229889-1+2*2^9*c.k,97134352414766+c.lower,97134731015320+c.upper)) = pointBounds16024 := by
 decide +kernel
def cuts16025 : List PrefixCut := [⟨18,115165055,115165130⟩,
⟨83,530740660,530741000⟩,
⟨128,815229087,815229613⟩]
theorem checked16025 : checkPrefixCuts (2^48) 2104360961 9 Manual.Count131072.C016025.packed 128 cuts16025 = true := by
 decide +kernel
def pointBounds16025 : List (Nat × Nat × Nat) := [(2104379392,97135290350383,97135668951544),(2104445952,97135705925988,97136084527414)]
theorem point_links_checked16025 : (cuts16025.take 2).map (fun c => (2104360961-1+2*2^9*c.k,97135175185328+c.lower,97135553786414+c.upper)) = pointBounds16025 := by
 decide +kernel
def cuts16026 : List PrefixCut := [⟨20,128398949,128399031⟩,
⟨85,548094473,548094828⟩,
⟨128,825476693,825477220⟩]
theorem checked16026 : checkPrefixCuts (2^48) 2104492033 9 Manual.Count131072.C016026.packed 128 cuts16026 = true := by
 decide +kernel
def pointBounds16026 : List (Nat × Nat × Nat) := [(2104512512,97136118813364,97136497415058),(2104579072,97136538508888,97136917110855)]
theorem point_links_checked16026 : (cuts16026.take 2).map (fun c => (2104492033-1+2*2^9*c.k,97135990414415+c.lower,97136369016027+c.upper)) = pointBounds16026 := by
 decide +kernel
def cuts16027 : List PrefixCut := [⟨22,138956378,138956470⟩,
⟨87,556351690,556352053⟩,
⟨128,825157475,825158011⟩]
theorem checked16027 : checkPrefixCuts (2^48) 2104623105 9 Manual.Count131072.C016027.packed 128 cuts16027 = true := by
 decide +kernel
def pointBounds16027 : List (Nat × Nat × Nat) := [(2104645632,97136954847486,97137333449717),(2104712192,97137372242798,97137750845300)]
theorem point_links_checked16027 : (cuts16027.take 2).map (fun c => (2104623105-1+2*2^9*c.k,97136815891108+c.lower,97137194493247+c.upper)) = pointBounds16027 := by
 decide +kernel
def cuts16028 : List PrefixCut := [⟨24,159141237,159141336⟩,
⟨89,575707822,575708188⟩,
⟨128,824036727,824037251⟩]
theorem checked16028 : checkPrefixCuts (2^48) 2104754177 9 Manual.Count131072.C016028.packed 128 cuts16028 = true := by
 decide +kernel
def pointBounds16028 : List (Nat × Nat × Nat) := [(2104778752,97137800189820,97138178792594),(2104845312,97138216756405,97138595359446)]
theorem point_links_checked16028 : (cuts16028.take 2).map (fun c => (2104754177-1+2*2^9*c.k,97137641048583+c.lower,97138019651258+c.upper)) = pointBounds16028 := by
 decide +kernel
def cuts16029 : List PrefixCut := [⟨26,167154681,167154787⟩,
⟨91,583561198,583561574⟩,
⟨128,816764430,816764957⟩]
theorem checked16029 : checkPrefixCuts (2^48) 2104885249 9 Manual.Count131072.C016029.packed 128 cuts16029 = true := by
 decide +kernel
def pointBounds16029 : List (Nat × Nat × Nat) := [(2104911872,97138632239991,97139010843296),(2104978432,97139048646508,97139427250083)]
theorem point_links_checked16029 : (cuts16029.take 2).map (fun c => (2104885249-1+2*2^9*c.k,97138465085310+c.lower,97138843688509+c.upper)) = pointBounds16029 := by
 decide +kernel
def cuts16030 : List PrefixCut := [⟨28,180114561,180114675⟩,
⟨93,599035258,599035639⟩,
⟨128,820190052,820190572⟩]
theorem checked16030 : checkPrefixCuts (2^48) 2105016321 9 Manual.Count131072.C016030.packed 128 cuts16030 = true := by
 decide +kernel
def pointBounds16030 : List (Nat × Nat × Nat) := [(2105044992,97139461964301,97139840568141),(2105111552,97139880884998,97140259489105)]
theorem point_links_checked16030 : (cuts16030.take 2).map (fun c => (2105016321-1+2*2^9*c.k,97139281849740+c.lower,97139660453466+c.upper)) = pointBounds16030 := by
 decide +kernel
def cuts16031 : List PrefixCut := [⟨30,194944708,194944835⟩,
⟨95,607688485,607688880⟩,
⟨128,816528939,816529470⟩]
theorem checked16031 : checkPrefixCuts (2^48) 2105147393 9 Manual.Count131072.C016031.packed 128 cuts16031 = true := by
 decide +kernel
def pointBounds16031 : List (Nat × Nat × Nat) := [(2105178112,97140296984500,97140675588873),(2105244672,97140709728277,97141088332918)]
theorem point_links_checked16031 : (cuts16031.take 2).map (fun c => (2105147393-1+2*2^9*c.k,97140102039792+c.lower,97140480644038+c.upper)) = pointBounds16031 := by
 decide +kernel
def cuts16032 : List PrefixCut := [⟨32,204157700,204157835⟩,
⟨97,622624255,622624657⟩,
⟨128,823028961,823029493⟩]
theorem checked16032 : checkPrefixCuts (2^48) 2105278465 9 Manual.Count131072.C016032.packed 128 cuts16032 = true := by
 decide +kernel
def pointBounds16032 : List (Nat × Nat × Nat) := [(2105311232,97141122726431,97141501331343),(2105377792,97141541192986,97141919798165)]
theorem point_links_checked16032 : (cuts16032.take 2).map (fun c => (2105278465-1+2*2^9*c.k,97140918568731+c.lower,97141297173508+c.upper)) = pointBounds16032 := by
 decide +kernel
def cuts16033 : List PrefixCut := [⟨34,214171626,214171770⟩,
⟨99,628200209,628200619⟩,
⟨128,814689253,814689783⟩]
theorem checked16033 : checkPrefixCuts (2^48) 2105409537 9 Manual.Count131072.C016033.packed 128 cuts16033 = true := by
 decide +kernel
def pointBounds16033 : List (Nat × Nat × Nat) := [(2105444352,97141955769318,97142334374771),(2105510912,97142369797901,97142748403620)]
theorem point_links_checked16033 : (cuts16033.take 2).map (fun c => (2105409537-1+2*2^9*c.k,97141741597692+c.lower,97142120203001+c.upper)) = pointBounds16033 := by
 decide +kernel
def cuts16034 : List PrefixCut := [⟨36,232873689,232873840⟩,
⟨101,649148492,649148913⟩,
⟨128,820253148,820253680⟩]
theorem checked16034 : checkPrefixCuts (2^48) 2105540609 9 Manual.Count131072.C016034.packed 128 cuts16034 = true := by
 decide +kernel
def pointBounds16034 : List (Nat × Nat × Nat) := [(2105577472,97142789160634,97143167766624),(2105644032,97143205435437,97143584041697)]
theorem point_links_checked16034 : (cuts16034.take 2).map (fun c => (2105540609-1+2*2^9*c.k,97142556286945+c.lower,97142934892784+c.upper)) = pointBounds16034 := by
 decide +kernel
def cuts16035 : List PrefixCut := [⟨38,245424360,245424517⟩,
⟨103,654321079,654321496⟩,
⟨128,816993972,816994494⟩]
theorem checked16035 : checkPrefixCuts (2^48) 2105671681 9 Manual.Count131072.C016035.packed 128 cuts16035 = true := by
 decide +kernel
def pointBounds16035 : List (Nat × Nat × Nat) := [(2105710592,97143621964453,97144000570981),(2105777152,97144030861172,97144409467960)]
theorem point_links_checked16035 : (cuts16035.take 2).map (fun c => (2105671681-1+2*2^9*c.k,97143376540093+c.lower,97143755146464+c.upper)) = pointBounds16035 := by
 decide +kernel
def cuts16036 : List PrefixCut := [⟨40,252092187,252092351⟩,
⟨105,665106472,665106906⟩,
⟨128,813200351,813200877⟩]
theorem checked16036 : checkPrefixCuts (2^48) 2105802753 9 Manual.Count131072.C016036.packed 128 cuts16036 = true := by
 decide +kernel
def pointBounds16036 : List (Nat × Nat × Nat) := [(2105843712,97144445626252,97144824233309),(2105910272,97144858640537,97145237247864)]
theorem point_links_checked16036 : (cuts16036.take 2).map (fun c => (2105802753-1+2*2^9*c.k,97144193534065+c.lower,97144572140958+c.upper)) = pointBounds16036 := by
 decide +kernel
def cuts16037 : List PrefixCut := [⟨42,262902590,262902757⟩,
⟨107,674153379,674153811⟩,
⟨128,813818006,813818526⟩]
theorem checked16037 : checkPrefixCuts (2^48) 2105933825 9 Manual.Count131072.C016037.packed 128 cuts16037 = true := by
 decide +kernel
def pointBounds16037 : List (Nat × Nat × Nat) := [(2105976832,97145269637006,97145648244592),(2106043392,97145680887795,97146059495646)]
theorem point_links_checked16037 : (cuts16037.take 2).map (fun c => (2105933825-1+2*2^9*c.k,97145006734416+c.lower,97145385341835+c.upper)) = pointBounds16037 := by
 decide +kernel
def cuts16038 : List PrefixCut := [⟨44,279725793,279725973⟩,
⟨109,699236585,699237036⟩,
⟨128,817509729,817510254⟩]
theorem checked16038 : checkPrefixCuts (2^48) 2106064897 9 Manual.Count131072.C016038.packed 128 cuts16038 = true := by
 decide +kernel
def pointBounds16038 : List (Nat × Nat × Nat) := [(2106109952,97146100278215,97146478886334),(2106176512,97146519789007,97146898397397)]
theorem point_links_checked16038 : (cuts16038.take 2).map (fun c => (2106064897-1+2*2^9*c.k,97145820552422+c.lower,97146199160361+c.upper)) = pointBounds16038 := by
 decide +kernel
def cuts16039 : List PrefixCut := [⟨46,292404040,292404225⟩,
⟨111,706943677,706944126⟩,
⟨128,813984173,813984690⟩]
theorem checked16039 : checkPrefixCuts (2^48) 2106195969 9 Manual.Count131072.C016039.packed 128 cuts16039 = true := by
 decide +kernel
def pointBounds16039 : List (Nat × Nat × Nat) := [(2106243072,97146930466191,97147309074840),(2106309632,97147345005828,97147723614741)]
theorem point_links_checked16039 : (cuts16039.take 2).map (fun c => (2106195969-1+2*2^9*c.k,97146638062151+c.lower,97147016670615+c.upper)) = pointBounds16039 := by
 decide +kernel
def cuts16040 : List PrefixCut := [⟨48,307352418,307352619⟩,
⟨113,718391490,718391961⟩,
⟨128,815269773,815270307⟩]
theorem checked16040 : checkPrefixCuts (2^48) 2106327041 9 Manual.Count131072.C016040.packed 128 cuts16040 = true := by
 decide +kernel
def pointBounds16040 : List (Nat × Nat × Nat) := [(2106376192,97147759398742,97148138007924),(2106442752,97148170437814,97148549047266)]
theorem point_links_checked16040 : (cuts16040.take 2).map (fun c => (2106327041-1+2*2^9*c.k,97147452046324+c.lower,97147830655305+c.upper)) = pointBounds16040 := by
 decide +kernel
def cuts16041 : List PrefixCut := [⟨50,311208184,311208384⟩,
⟨115,720217047,720217511⟩,
⟨128,799719067,799719584⟩]
theorem checked16041 : checkPrefixCuts (2^48) 2106458113 9 Manual.Count131072.C016041.packed 128 cuts16041 = true := by
 decide +kernel
def pointBounds16041 : List (Nat × Nat × Nat) := [(2106509312,97148578524281,97148957133996),(2106575872,97148987533144,97149366143123)]
theorem point_links_checked16041 : (cuts16041.take 2).map (fun c => (2106458113-1+2*2^9*c.k,97148267316097+c.lower,97148645925612+c.upper)) = pointBounds16041 := by
 decide +kernel
def cuts16042 : List PrefixCut := [⟨52,331898987,331899201⟩,
⟨117,739545933,739546404⟩,
⟨128,807419032,807419547⟩]
theorem checked16042 : checkPrefixCuts (2^48) 2106589185 9 Manual.Count131072.C016042.packed 128 cuts16042 = true := by
 decide +kernel
def pointBounds16042 : List (Nat × Nat × Nat) := [(2106642432,97149398934151,97149777544397),(2106708992,97149806581097,97150185191600)]
theorem point_links_checked16042 : (cuts16042.take 2).map (fun c => (2106589185-1+2*2^9*c.k,97149067035164+c.lower,97149445645196+c.upper)) = pointBounds16042 := by
 decide +kernel
def cuts16043 : List PrefixCut := [⟨54,346975738,346975960⟩,
⟨119,759673883,759674369⟩,
⟨128,814984310,814984833⟩]
theorem checked16043 : checkPrefixCuts (2^48) 2106720257 9 Manual.Count131072.C016043.packed 128 cuts16043 = true := by
 decide +kernel
def pointBounds16043 : List (Nat × Nat × Nat) := [(2106775552,97150221429934,97150600040703),(2106842112,97150634128079,97151012739112)]
theorem point_links_checked16043 : (cuts16043.take 2).map (fun c => (2106720257-1+2*2^9*c.k,97149874454196+c.lower,97150253064743+c.upper)) = pointBounds16043 := by
 decide +kernel
def cuts16044 : List PrefixCut := [⟨56,360714516,360714751⟩,
⟨121,779398258,779398762⟩,
⟨128,823750703,823751237⟩]
theorem checked16044 : checkPrefixCuts (2^48) 2106851329 9 Manual.Count131072.C016044.packed 128 cuts16044 = true := by
 decide +kernel
def pointBounds16044 : List (Nat × Nat × Nat) := [(2106908672,97151050153022,97151428764327),(2106975232,97151468836764,97151847448338)]
theorem point_links_checked16044 : (cuts16044.take 2).map (fun c => (2106851329-1+2*2^9*c.k,97150689438506+c.lower,97151068049576+c.upper)) = pointBounds16044 := by
 decide +kernel
def cuts16045 : List PrefixCut := [⟨58,364565947,364566183⟩,
⟨123,774139381,774139883⟩,
⟨128,806867295,806867818⟩]
theorem checked16045 : checkPrefixCuts (2^48) 2106982401 9 Manual.Count131072.C016045.packed 128 cuts16045 = true := by
 decide +kernel
def pointBounds16045 : List (Nat × Nat × Nat) := [(2107041792,97151877755156,97152256366996),(2107108352,97152287328590,97152665940696)]
theorem point_links_checked16045 : (cuts16045.take 2).map (fun c => (2106982401-1+2*2^9*c.k,97151513189209+c.lower,97151891800813+c.upper)) = pointBounds16045 := by
 decide +kernel
def cuts16046 : List PrefixCut := [⟨60,384046034,384046279⟩,
⟨125,800539559,800540073⟩,
⟨128,817770729,817771254⟩]
theorem checked16046 : checkPrefixCuts (2^48) 2107113473 9 Manual.Count131072.C016046.packed 128 cuts16046 = true := by
 decide +kernel
def pointBounds16046 : List (Nat × Nat × Nat) := [(2107174912,97152704102538,97153082714910),(2107241472,97153120596063,97153499208704)]
theorem point_links_checked16046 : (cuts16046.take 2).map (fun c => (2107113473-1+2*2^9*c.k,97152320056504+c.lower,97152698668631+c.upper)) = pointBounds16046 := by
 decide +kernel
def cuts16047 : List PrefixCut := [⟨62,399783541,399783795⟩,
⟨127,813712986,813713505⟩,
⟨128,820792015,820792538⟩]
theorem checked16047 : checkPrefixCuts (2^48) 2107244545 9 Manual.Count131072.C016047.packed 128 cuts16047 = true := by
 decide +kernel
def pointBounds16047 : List (Nat × Nat × Nat) := [(2107308032,97153537610774,97153916223680),(2107374592,97153951540219,97154330153390)]
theorem point_links_checked16047 : (cuts16047.take 2).map (fun c => (2107244545-1+2*2^9*c.k,97153137827233+c.lower,97153516439885+c.upper)) = pointBounds16047 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000188
