import PlattAssemblyKernel
import PlattCertificates.Count131072.C013968
import PlattCertificates.Count131072.C013969
import PlattCertificates.Count131072.C013970
import PlattCertificates.Count131072.C013971
import PlattCertificates.Count131072.C013972
import PlattCertificates.Count131072.C013973
import PlattCertificates.Count131072.C013974
import PlattCertificates.Count131072.C013975
import PlattCertificates.Count131072.C013976
import PlattCertificates.Count131072.C013977
import PlattCertificates.Count131072.C013978
import PlattCertificates.Count131072.C013979
import PlattCertificates.Count131072.C013980
import PlattCertificates.Count131072.C013981
import PlattCertificates.Count131072.C013982
import PlattCertificates.Count131072.C013983
import PlattCertificates.Count131072.C013984
import PlattCertificates.Count131072.C013985
import PlattCertificates.Count131072.C013986
import PlattCertificates.Count131072.C013987
import PlattCertificates.Count131072.C013988
import PlattCertificates.Count131072.C013989
import PlattCertificates.Count131072.C013990
import PlattCertificates.Count131072.C013991
import PlattCertificates.Count131072.C013992
import PlattCertificates.Count131072.C013993
import PlattCertificates.Count131072.C013994
import PlattCertificates.Count131072.C013995
import PlattCertificates.Count131072.C013996
import PlattCertificates.Count131072.C013997
import PlattCertificates.Count131072.C013998
import PlattCertificates.Count131072.C013999
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000124
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13968 : List PrefixCut := [⟨43,315414480,315414699⟩,
⟨99,727466946,727467452⟩,
⟨128,937476826,937477480⟩]
theorem checked13968 : checkPrefixCuts (2^48) 1834745857 9 Manual.Count131072.C013968.packed 128 cuts13968 = true := by
 decide +kernel
def pointBounds13968 : List (Nat × Nat × Nat) := [(1834789888,95332079957846,95332457355200),(1834847232,95332492010312,95332869407953)]
theorem point_links_checked13968 : (cuts13968.take 2).map (fun c => (1834745857-1+2*2^9*c.k,95331764543366+c.lower,95332141940501+c.upper)) = pointBounds13968 := by
 decide +kernel
def cuts13969 : List PrefixCut := [⟨27,193592610,193592750⟩,
⟨83,620192157,620192591⟩,
⟨128,955203722,955204391⟩]
theorem checked13969 : checkPrefixCuts (2^48) 1834876929 9 Manual.Count131072.C013969.packed 128 cuts13969 = true := by
 decide +kernel
def pointBounds13969 : List (Nat × Nat × Nat) := [(1834904576,95332895612802,95333273010731),(1834961920,95333322212349,95333699610572)]
theorem point_links_checked13969 : (cuts13969.take 2).map (fun c => (1834876929-1+2*2^9*c.k,95332702020192+c.lower,95333079417981+c.upper)) = pointBounds13969 := by
 decide +kernel
def cuts13970 : List PrefixCut := [⟨11,82677831,82677889⟩,
⟨67,498513600,498513941⟩,
⟨124,919551144,919551775⟩,
⟨128,949307030,949307683⟩]
theorem checked13970 : checkPrefixCuts (2^48) 1835008001 9 Manual.Count131072.C013970.packed 128 cuts13970 = true := by
 decide +kernel
def pointBounds13970 : List (Nat × Nat × Nat) := [(1835019264,95333739901745,95334117300261),(1835076608,95334155737514,95334533136313),(1835134976,95334576775058,95334954174147)]
theorem point_links_checked13970 : (cuts13970.take 3).map (fun c => (1835008001-1+2*2^9*c.k,95333657223914+c.lower,95334034622372+c.upper)) = pointBounds13970 := by
 decide +kernel
def cuts13971 : List PrefixCut := [⟨53,388354064,388354334⟩,
⟨110,809671670,809672231⟩,
⟨128,944637697,944638352⟩]
theorem checked13971 : checkPrefixCuts (2^48) 1835139073 9 Manual.Count131072.C013971.packed 128 cuts13971 = true := by
 decide +kernel
def pointBounds13971 : List (Nat × Nat × Nat) := [(1835193344,95334994885008,95335372284389),(1835251712,95335416202614,95335793602286)]
theorem point_links_checked13971 : (cuts13971.take 2).map (fun c => (1835139073-1+2*2^9*c.k,95334606530944+c.lower,95334983930055+c.upper)) = pointBounds13971 := by
 decide +kernel
def cuts13972 : List PrefixCut := [⟨39,291399327,291399529⟩,
⟨96,707782390,707782885⟩,
⟨128,940123009,940123664⟩]
theorem checked13972 : checkPrefixCuts (2^48) 1835270145 9 Manual.Count131072.C013972.packed 128 cuts13972 = true := by
 decide +kernel
def pointBounds13972 : List (Nat × Nat × Nat) := [(1835310080,95335842567968,95336219967936),(1835368448,95336258951031,95336636351292)]
theorem point_links_checked13972 : (cuts13972.take 2).map (fun c => (1835270145-1+2*2^9*c.k,95335551168641+c.lower,95335928568407+c.upper)) = pointBounds13972 := by
 decide +kernel
def cuts13973 : List PrefixCut := [⟨25,183262464,183262592⟩,
⟨82,608053546,608053969⟩,
⟨128,948643381,948644041⟩]
theorem checked13973 : checkPrefixCuts (2^48) 1835401217 9 Manual.Count131072.C013973.packed 128 cuts13973 = true := by
 decide +kernel
def pointBounds13973 : List (Nat × Nat × Nat) := [(1835426816,95336674554114,95337051954663),(1835485184,95337099345196,95337476746040)]
theorem point_links_checked13973 : (cuts13973.take 2).map (fun c => (1835401217-1+2*2^9*c.k,95336491291650+c.lower,95336868692071+c.upper)) = pointBounds13973 := by
 decide +kernel
def cuts13974 : List PrefixCut := [⟨11,79280584,79280640⟩,
⟨68,495150753,495151103⟩,
⟨125,910240923,910241564⟩,
⟨128,931554767,931555422⟩]
theorem checked13974 : checkPrefixCuts (2^48) 1835532289 9 Manual.Count131072.C013974.packed 128 cuts13974 = true := by
 decide +kernel
def pointBounds13974 : List (Nat × Nat × Nat) := [(1835543552,95337519215615,95337896616752),(1835601920,95337935085784,95338312487215),(1835660288,95338350175954,95338727577676)]
theorem point_links_checked13974 : (cuts13974.take 3).map (fun c => (1835532289-1+2*2^9*c.k,95337439935031+c.lower,95337817336112+c.upper)) = pointBounds13974 := by
 decide +kernel
def cuts13975 : List PrefixCut := [⟨54,388089792,388090059⟩,
⟨111,803613606,803614159⟩,
⟨128,937467764,937468411⟩]
theorem checked13975 : checkPrefixCuts (2^48) 1835663361 9 Manual.Count131072.C013975.packed 128 cuts13975 = true := by
 decide +kernel
def pointBounds13975 : List (Nat × Nat × Nat) := [(1835718656,95338759579590,95339136981593),(1835777024,95339175103404,95339552505693)]
theorem point_links_checked13975 : (cuts13975.take 2).map (fun c => (1835663361-1+2*2^9*c.k,95338371489798+c.lower,95338748891534+c.upper)) = pointBounds13975 := by
 decide +kernel
def cuts13976 : List PrefixCut := [⟨40,291162715,291162915⟩,
⟨97,713252788,713253283⟩,
⟨128,944760402,944761059⟩]
theorem checked13976 : checkPrefixCuts (2^48) 1835794433 9 Manual.Count131072.C013976.packed 128 cuts13976 = true := by
 decide +kernel
def pointBounds13976 : List (Nat × Nat × Nat) := [(1835835392,95339600120277,95339977522860),(1835893760,95340022210350,95340399613228)]
theorem point_links_checked13976 : (cuts13976.take 2).map (fun c => (1835794433-1+2*2^9*c.k,95339308957562+c.lower,95339686359945+c.upper)) = pointBounds13976 := by
 decide +kernel
def cuts13977 : List PrefixCut := [⟨26,188882688,188882819⟩,
⟨83,608952938,608953358⟩,
⟨128,941320200,941320849⟩]
theorem checked13977 : checkPrefixCuts (2^48) 1835925505 9 Manual.Count131072.C013977.packed 128 cuts13977 = true := by
 decide +kernel
def pointBounds13977 : List (Nat × Nat × Nat) := [(1835952128,95340442600652,95340820003823),(1836010496,95340862670902,95341240074362)]
theorem point_links_checked13977 : (cuts13977.take 2).map (fun c => (1835925505-1+2*2^9*c.k,95340253717964+c.lower,95340631121004+c.upper)) = pointBounds13977 := by
 decide +kernel
def cuts13978 : List PrefixCut := [⟨12,87842922,87842983⟩,
⟨69,501754381,501754730⟩,
⟨126,935427856,935428498⟩,
⟨128,950757174,950757827⟩]
theorem checked13978 : checkPrefixCuts (2^48) 1836056577 9 Manual.Count131072.C013978.packed 128 cuts13978 = true := by
 decide +kernel
def pointBounds13978 : List (Nat × Nat × Nat) := [(1836068864,95341282881086,95341660284836),(1836127232,95341696792545,95342074196583),(1836185600,95342130466020,95342507870351)]
theorem point_links_checked13978 : (cuts13978.take 3).map (fun c => (1836056577-1+2*2^9*c.k,95341195038164+c.lower,95341572441853+c.upper)) = pointBounds13978 := by
 decide +kernel
def cuts13979 : List PrefixCut := [⟨55,404534237,404534515⟩,
⟨112,812887978,812888544⟩,
⟨128,929382927,929383575⟩]
theorem checked13979 : checkPrefixCuts (2^48) 1836187649 9 Manual.Count131072.C013979.packed 128 cuts13979 = true := by
 decide +kernel
def pointBounds13979 : List (Nat × Nat × Nat) := [(1836243968,95342550329575,95342927734195),(1836302336,95342958683316,95343336088224)]
theorem point_links_checked13979 : (cuts13979.take 2).map (fun c => (1836187649-1+2*2^9*c.k,95342145795338+c.lower,95342523199680+c.upper)) = pointBounds13979 := by
 decide +kernel
def cuts13980 : List PrefixCut := [⟨41,304568207,304568417⟩,
⟨98,722245751,722246248⟩,
⟨128,944031065,944031713⟩]
theorem checked13980 : checkPrefixCuts (2^48) 1836318721 9 Manual.Count131072.C013980.packed 128 cuts13980 = true := by
 decide +kernel
def pointBounds13980 : List (Nat × Nat × Nat) := [(1836360704,95343379746472,95343757151672),(1836419072,95343797424016,95344174829503)]
theorem point_links_checked13980 : (cuts13980.take 2).map (fun c => (1836318721-1+2*2^9*c.k,95343075178265+c.lower,95343452583255+c.upper)) = pointBounds13980 := by
 decide +kernel
def cuts13981 : List PrefixCut := [⟨27,198791253,198791391⟩,
⟨84,606633340,606633764⟩,
⟨128,934001346,934001996⟩]
theorem checked13981 : checkPrefixCuts (2^48) 1836449793 9 Manual.Count131072.C013981.packed 128 cuts13981 = true := by
 decide +kernel
def pointBounds13981 : List (Nat × Nat × Nat) := [(1836477440,95344218000583,95344595406359),(1836535808,95344625842670,95345003248732)]
theorem point_links_checked13981 : (cuts13981.take 2).map (fun c => (1836449793-1+2*2^9*c.k,95344019209330+c.lower,95344396614968+c.upper)) = pointBounds13981 := by
 decide +kernel
def cuts13982 : List PrefixCut := [⟨13,90116717,90116780⟩,
⟨70,514637899,514638255⟩,
⟨127,943436663,943437312⟩,
⟨128,951558880,951559534⟩]
theorem checked13982 : checkPrefixCuts (2^48) 1836580865 9 Manual.Count131072.C013982.packed 128 cuts13982 = true := by
 decide +kernel
def pointBounds13982 : List (Nat × Nat × Nat) := [(1836594176,95345043327393,95345420733744),(1836652544,95345467848575,95345845255219),(1836710912,95345896647339,95346274054276)]
theorem point_links_checked13982 : (cuts13982.take 3).map (fun c => (1836580865-1+2*2^9*c.k,95344953210676+c.lower,95345330616964+c.upper)) = pointBounds13982 := by
 decide +kernel
def cuts13983 : List PrefixCut := [⟨56,413919936,413920223⟩,
⟨113,829972354,829972928⟩,
⟨128,942603036,942603688⟩]
theorem checked13983 : checkPrefixCuts (2^48) 1836711937 9 Manual.Count131072.C013983.packed 128 cuts13983 = true := by
 decide +kernel
def pointBounds13983 : List (Nat × Nat × Nat) := [(1836769280,95346318689492,95346696096721),(1836827648,95346734741910,95347112149426)]
theorem point_links_checked13983 : (cuts13983.take 2).map (fun c => (1836711937-1+2*2^9*c.k,95345904769556+c.lower,95346282176498+c.upper)) = pointBounds13983 := by
 decide +kernel
def cuts13984 : List PrefixCut := [⟨42,301263178,301263388⟩,
⟨99,725410433,725410940⟩,
⟨128,934720850,934721503⟩]
theorem checked13984 : checkPrefixCuts (2^48) 1836843009 9 Manual.Count131072.C013984.packed 128 cuts13984 = true := by
 decide +kernel
def pointBounds13984 : List (Nat × Nat × Nat) := [(1836886016,95347148635770,95347526043574),(1836944384,95347572783025,95347950191126)]
theorem point_links_checked13984 : (cuts13984.take 2).map (fun c => (1836843009-1+2*2^9*c.k,95346847372592+c.lower,95347224780186+c.upper)) = pointBounds13984 := by
 decide +kernel
def cuts13985 : List PrefixCut := [⟨28,206242553,206242697⟩,
⟨85,633274023,633274464⟩,
⟨128,952427832,952428500⟩]
theorem checked13985 : checkPrefixCuts (2^48) 1836974081 9 Manual.Count131072.C013985.packed 128 cuts13985 = true := by
 decide +kernel
def pointBounds13985 : List (Nat × Nat × Nat) := [(1837002752,95347988335995,95348365744386),(1837061120,95348415367465,95348792776153)]
theorem point_links_checked13985 : (cuts13985.take 2).map (fun c => (1836974081-1+2*2^9*c.k,95347782093442+c.lower,95348159501689+c.upper)) = pointBounds13985 := by
 decide +kernel
def cuts13986 : List PrefixCut := [⟨14,102348252,102348322⟩,
⟨71,530271921,530272284⟩,
⟨128,940563126,940563772⟩]
theorem checked13986 : checkPrefixCuts (2^48) 1837105153 9 Manual.Count131072.C013986.packed 128 cuts13986 = true := by
 decide +kernel
def pointBounds13986 : List (Nat × Nat × Nat) := [(1837119488,95348836869526,95349214278511),(1837177856,95349264793195,95349642202473),(1837236224,95349675084400,95350052493961)]
theorem point_links_checked13986 : (cuts13986.take 3).map (fun c => (1837105153-1+2*2^9*c.k,95348734521274+c.lower,95349111930189+c.upper)) = pointBounds13986 := by
 decide +kernel
def cuts13987 : List PrefixCut := [⟨57,425751649,425751945⟩,
⟨114,847966222,847966815⟩,
⟨128,946164400,946165062⟩]
theorem checked13987 : checkPrefixCuts (2^48) 1837236225 9 Manual.Count131072.C013987.packed 128 cuts13987 = true := by
 decide +kernel
def pointBounds13987 : List (Nat × Nat × Nat) := [(1837294592,95350100836049,95350478245906),(1837352960,95350523050622,95350900460776)]
theorem point_links_checked13987 : (cuts13987.take 2).map (fun c => (1837236225-1+2*2^9*c.k,95349675084400+c.lower,95350052493961+c.upper)) = pointBounds13987 := by
 decide +kernel
def cuts13988 : List PrefixCut := [⟨43,322011334,322011555⟩,
⟨100,736845903,736846416⟩,
⟨128,939050034,939050688⟩]
theorem checked13988 : checkPrefixCuts (2^48) 1837367297 9 Manual.Count131072.C013988.packed 128 cuts13988 = true := by
 decide +kernel
def pointBounds13988 : List (Nat × Nat × Nat) := [(1837411328,95350943260134,95351320670578),(1837469696,95351358094703,95351735505439)]
theorem point_links_checked13988 : (cuts13988.take 2).map (fun c => (1837367297-1+2*2^9*c.k,95350621248800+c.lower,95350998659023+c.upper)) = pointBounds13988 := by
 decide +kernel
def cuts13989 : List PrefixCut := [⟨29,219663701,219663851⟩,
⟨86,637076046,637076485⟩,
⟨128,941740330,941740983⟩]
theorem checked13989 : checkPrefixCuts (2^48) 1837498369 9 Manual.Count131072.C013989.packed 128 cuts13989 = true := by
 decide +kernel
def pointBounds13989 : List (Nat × Nat × Nat) := [(1837528064,95351779962535,95352157373562),(1837586432,95352197374880,95352574786196)]
theorem point_links_checked13989 : (cuts13989.take 2).map (fun c => (1837498369-1+2*2^9*c.k,95351560298834+c.lower,95351937709711+c.upper)) = pointBounds13989 := by
 decide +kernel
def cuts13990 : List PrefixCut := [⟨15,113194233,113194313⟩,
⟨72,527669769,527670134⟩,
⟨128,936618395,936619045⟩]
theorem checked13990 : checkPrefixCuts (2^48) 1837629441 9 Manual.Count131072.C013990.packed 128 cuts13990 = true := by
 decide +kernel
def pointBounds13990 : List (Nat × Nat × Nat) := [(1837644800,95352615233397,95352992645007),(1837703168,95353029708933,95353407120828)]
theorem point_links_checked13990 : (cuts13990.take 2).map (fun c => (1837629441-1+2*2^9*c.k,95352502039164+c.lower,95352879450694+c.upper)) = pointBounds13990 := by
 decide +kernel
def cuts13991 : List PrefixCut := [⟨1,8117578,8117584⟩,
⟨58,435585409,435585708⟩,
⟨115,843435839,843436421⟩,
⟨128,944975315,944975965⟩]
theorem checked13991 : checkPrefixCuts (2^48) 1837760513 9 Manual.Count131072.C013991.packed 128 cuts13991 = true := by
 decide +kernel
def pointBounds13991 : List (Nat × Nat × Nat) := [(1837761536,95353446775137,95353824187323),(1837819904,95353874242968,95354251655447),(1837878272,95354282093398,95354659506160)]
theorem point_links_checked13991 : (cuts13991.take 3).map (fun c => (1837760513-1+2*2^9*c.k,95353438657559+c.lower,95353816069739+c.upper)) = pointBounds13991 := by
 decide +kernel
def cuts13992 : List PrefixCut := [⟨44,321613054,321613279⟩,
⟨101,734185105,734185611⟩,
⟨128,930971557,930972202⟩]
theorem checked13992 : checkPrefixCuts (2^48) 1837891585 9 Manual.Count131072.C013992.packed 128 cuts13992 = true := by
 decide +kernel
def pointBounds13992 : List (Nat × Nat × Nat) := [(1837936640,95354705245928,95355082658983),(1837995008,95355117817979,95355495231315)]
theorem point_links_checked13992 : (cuts13992.take 2).map (fun c => (1837891585-1+2*2^9*c.k,95354383632874+c.lower,95354761045704+c.upper)) = pointBounds13992 := by
 decide +kernel
def cuts13993 : List PrefixCut := [⟨30,226339075,226339234⟩,
⟨87,644244608,644245056⟩,
⟨128,948668755,948669417⟩]
theorem checked13993 : checkPrefixCuts (2^48) 1838022657 9 Manual.Count131072.C013993.packed 128 cuts13993 = true := by
 decide +kernel
def pointBounds13993 : List (Nat × Nat × Nat) := [(1838053376,95355540943506,95355918357140),(1838111744,95355958849039,95356336262962)]
theorem point_links_checked13993 : (cuts13993.take 2).map (fun c => (1838022657-1+2*2^9*c.k,95355314604431+c.lower,95355692017906+c.upper)) = pointBounds13993 := by
 decide +kernel
def cuts13994 : List PrefixCut := [⟨16,114693200,114693282⟩,
⟨73,530275365,530275734⟩,
⟨128,925326356,925327007⟩]
theorem checked13994 : checkPrefixCuts (2^48) 1838153729 9 Manual.Count131072.C013994.packed 128 cuts13994 = true := by
 decide +kernel
def pointBounds13994 : List (Nat × Nat × Nat) := [(1838170112,95356377966386,95356755380605),(1838228480,95356793548551,95357170963057)]
theorem point_links_checked13994 : (cuts13994.take 2).map (fun c => (1838153729-1+2*2^9*c.k,95356263273186+c.lower,95356640687323+c.upper)) = pointBounds13994 := by
 decide +kernel
def cuts13995 : List PrefixCut := [⟨2,14239986,14239996⟩,
⟨59,432704964,432705268⟩,
⟨116,849931764,849932357⟩,
⟨128,937815649,937816304⟩]
theorem checked13995 : checkPrefixCuts (2^48) 1838284801 9 Manual.Count131072.C013995.packed 128 cuts13995 = true := by
 decide +kernel
def pointBounds13995 : List (Nat × Nat × Nat) := [(1838286848,95357202839528,95357580254326),(1838345216,95357621304506,95357998719598),(1838403584,95358038531306,95358415946687)]
theorem point_links_checked13995 : (cuts13995.take 3).map (fun c => (1838284801-1+2*2^9*c.k,95357188599542+c.lower,95357566014330+c.upper)) = pointBounds13995 := by
 decide +kernel
def cuts13996 : List PrefixCut := [⟨45,329176544,329176772⟩,
⟨102,750051296,750051818⟩,
⟨128,939585969,939586625⟩]
theorem checked13996 : checkPrefixCuts (2^48) 1838415873 9 Manual.Count131072.C013996.packed 128 cuts13996 = true := by
 decide +kernel
def pointBounds13996 : List (Nat × Nat × Nat) := [(1838461952,95358455591735,95358833007406),(1838520320,95358876466487,95359253882452)]
theorem point_links_checked13996 : (cuts13996.take 2).map (fun c => (1838415873-1+2*2^9*c.k,95358126415191+c.lower,95358503830634+c.upper)) = pointBounds13996 := by
 decide +kernel
def cuts13997 : List PrefixCut := [⟨31,226427569,226427724⟩,
⟨88,645132275,645132721⟩,
⟨128,944264556,944265208⟩]
theorem checked13997 : checkPrefixCuts (2^48) 1838546945 9 Manual.Count131072.C013997.packed 128 cuts13997 = true := by
 decide +kernel
def pointBounds13997 : List (Nat × Nat × Nat) := [(1838578688,95359292428729,95359669844983),(1838637056,95359711133435,95360088549980)]
theorem point_links_checked13997 : (cuts13997.take 2).map (fun c => (1838546945-1+2*2^9*c.k,95359066001160+c.lower,95359443417259+c.upper)) = pointBounds13997 := by
 decide +kernel
def cuts13998 : List PrefixCut := [⟨17,125988751,125988838⟩,
⟨74,546656944,546657330⟩,
⟨128,947105968,947106630⟩]
theorem checked13998 : checkPrefixCuts (2^48) 1838678017 9 Manual.Count131072.C013998.packed 128 cuts13998 = true := by
 decide +kernel
def pointBounds13998 : List (Nat × Nat × Nat) := [(1838695424,95360136254467,95360513671305),(1838753792,95360556922660,95360934339797)]
theorem point_links_checked13998 : (cuts13998.take 2).map (fun c => (1838678017-1+2*2^9*c.k,95360010265716+c.lower,95360387682467+c.upper)) = pointBounds13998 := by
 decide +kernel
def cuts13999 : List PrefixCut := [⟨3,25104205,25104223⟩,
⟨60,444214955,444215261⟩,
⟨117,852750808,852751392⟩,
⟨128,928517549,928518186⟩]
theorem checked13999 : checkPrefixCuts (2^48) 1838809089 9 Manual.Count131072.C013999.packed 128 cuts13999 = true := by
 decide +kernel
def pointBounds13999 : List (Nat × Nat × Nat) := [(1838812160,95360982475889,95361359893320),(1838870528,95361401586639,95361779004358),(1838928896,95361810122492,95362187540489)]
theorem point_links_checked13999 : (cuts13999.take 3).map (fun c => (1838809089-1+2*2^9*c.k,95360957371684+c.lower,95361334789097+c.upper)) = pointBounds13999 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000124
