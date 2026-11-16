import PlattAssemblyKernel
import PlattCertificates.Count131072.C011952
import PlattCertificates.Count131072.C011953
import PlattCertificates.Count131072.C011954
import PlattCertificates.Count131072.C011955
import PlattCertificates.Count131072.C011956
import PlattCertificates.Count131072.C011957
import PlattCertificates.Count131072.C011958
import PlattCertificates.Count131072.C011959
import PlattCertificates.Count131072.C011960
import PlattCertificates.Count131072.C011961
import PlattCertificates.Count131072.C011962
import PlattCertificates.Count131072.C011963
import PlattCertificates.Count131072.C011964
import PlattCertificates.Count131072.C011965
import PlattCertificates.Count131072.C011966
import PlattCertificates.Count131072.C011967
import PlattCertificates.Count131072.C011968
import PlattCertificates.Count131072.C011969
import PlattCertificates.Count131072.C011970
import PlattCertificates.Count131072.C011971
import PlattCertificates.Count131072.C011972
import PlattCertificates.Count131072.C011973
import PlattCertificates.Count131072.C011974
import PlattCertificates.Count131072.C011975
import PlattCertificates.Count131072.C011976
import PlattCertificates.Count131072.C011977
import PlattCertificates.Count131072.C011978
import PlattCertificates.Count131072.C011979
import PlattCertificates.Count131072.C011980
import PlattCertificates.Count131072.C011981
import PlattCertificates.Count131072.C011982
import PlattCertificates.Count131072.C011983
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000061
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts11952 : List PrefixCut := [⟨41,349306231,349306499⟩,
⟨89,768855883,768856474⟩,
⟨128,1097532603,1097533446⟩]
theorem checked11952 : checkPrefixCuts (2^48) 1570504705 9 Manual.Count131072.C011952.packed 128 cuts11952 = true := by
 decide +kernel
def pointBounds11952 : List (Nat × Nat × Nat) := [(1570546688,93272497115092,93272873010532),(1570595840,93272916664744,93273292560507)]
theorem point_links_checked11952 : (cuts11952.take 2).map (fun c => (1570504705-1+2*2^9*c.k,93272147808861+c.lower,93272523704033+c.upper)) = pointBounds11952 := by
 decide +kernel
def cuts11953 : List PrefixCut := [⟨9,78314877,78314940⟩,
⟨57,501960043,501960430⟩,
⟨105,918961530,918962235⟩,
⟨128,1116257659,1116258513⟩]
theorem checked11953 : checkPrefixCuts (2^48) 1570635777 9 Manual.Count131072.C011953.packed 128 cuts11953 = true := by
 decide +kernel
def pointBounds11953 : List (Nat × Nat × Nat) := [(1570644992,93273323656341,93273699552419),(1570694144,93273747301507,93274123197909),(1570743296,93274164302994,93274540199714)]
theorem point_links_checked11953 : (cuts11953.take 3).map (fun c => (1570635777-1+2*2^9*c.k,93273245341464+c.lower,93273621237479+c.upper)) = pointBounds11953 := by
 decide +kernel
def cuts11954 : List PrefixCut := [⟨25,214674872,214675036⟩,
⟨73,619465376,619465854⟩,
⟨121,1045566105,1045566908⟩,
⟨128,1105771020,1105771867⟩]
theorem checked11954 : checkPrefixCuts (2^48) 1570766849 9 Manual.Count131072.C011954.packed 128 cuts11954 = true := by
 decide +kernel
def pointBounds11954 : List (Nat × Nat × Nat) := [(1570792448,93274576273995,93274952171028),(1570841600,93274981064499,93275356961846),(1570890752,93275407165228,93275783062900)]
theorem point_links_checked11954 : (cuts11954.take 3).map (fun c => (1570766849-1+2*2^9*c.k,93274361599123+c.lower,93274737495992+c.upper)) = pointBounds11954 := by
 decide +kernel
def cuts11955 : List PrefixCut := [⟨41,356744397,356744667⟩,
⟨89,767947069,767947656⟩,
⟨128,1108008280,1108009128⟩]
theorem checked11955 : checkPrefixCuts (2^48) 1570897921 9 Manual.Count131072.C011955.packed 128 cuts11955 = true := by
 decide +kernel
def pointBounds11955 : List (Nat × Nat × Nat) := [(1570939904,93275824114540,93276200012526),(1570989056,93276235317212,93276611215515)]
theorem point_links_checked11955 : (cuts11955.take 2).map (fun c => (1570897921-1+2*2^9*c.k,93275467370143+c.lower,93275843267859+c.upper)) = pointBounds11955 := by
 decide +kernel
def cuts11956 : List PrefixCut := [⟨9,73278655,73278711⟩,
⟨57,497713638,497714016⟩,
⟨105,908519362,908520056⟩,
⟨128,1102720494,1102721336⟩]
theorem checked11956 : checkPrefixCuts (2^48) 1571028993 9 Manual.Count131072.C011956.packed 128 cuts11956 = true := by
 decide +kernel
def pointBounds11956 : List (Nat × Nat × Nat) := [(1571038208,93276648657078,93277024555698),(1571087360,93277073092061,93277448991003),(1571136512,93277483897785,93277859797043)]
theorem point_links_checked11956 : (cuts11956.take 3).map (fun c => (1571028993-1+2*2^9*c.k,93276575378423+c.lower,93276951276987+c.upper)) = pointBounds11956 := by
 decide +kernel
def cuts11957 : List PrefixCut := [⟨25,220533074,220533244⟩,
⟨73,641166060,641166553⟩,
⟨121,1048171310,1048172121⟩,
⟨128,1106390653,1106391509⟩]
theorem checked11957 : checkPrefixCuts (2^48) 1571160065 9 Manual.Count131072.C011957.packed 128 cuts11957 = true := by
 decide +kernel
def pointBounds11957 : List (Nat × Nat × Nat) := [(1571185664,93277898631991,93278274531567),(1571234816,93278319264977,93278695164876),(1571283968,93278726270227,93279102170444)]
theorem point_links_checked11957 : (cuts11957.take 3).map (fun c => (1571160065-1+2*2^9*c.k,93277678098917+c.lower,93278053998323+c.upper)) = pointBounds11957 := by
 decide +kernel
def cuts11958 : List PrefixCut := [⟨41,352176716,352176989⟩,
⟨89,769366857,769367450⟩,
⟨128,1104865018,1104865868⟩]
theorem checked11958 : checkPrefixCuts (2^48) 1571291137 9 Manual.Count131072.C011958.packed 128 cuts11958 = true := by
 decide +kernel
def pointBounds11958 : List (Nat × Nat × Nat) := [(1571333120,93279136666286,93279512566821),(1571382272,93279553856427,93279929757282)]
theorem point_links_checked11958 : (cuts11958.take 2).map (fun c => (1571291137-1+2*2^9*c.k,93278784489570+c.lower,93279160389832+c.upper)) = pointBounds11958 := by
 decide +kernel
def cuts11959 : List PrefixCut := [⟨9,79171290,79171351⟩,
⟨57,499917702,499918088⟩,
⟨105,912590879,912591582⟩,
⟨128,1109609123,1109609980⟩]
theorem checked11959 : checkPrefixCuts (2^48) 1571422209 9 Manual.Count131072.C011959.packed 128 cuts11959 = true := by
 decide +kernel
def pointBounds11959 : List (Nat × Nat × Nat) := [(1571431424,93279968525878,93280344427051),(1571480576,93280389272290,93280765173788),(1571529728,93280801945467,93281177847282)]
theorem point_links_checked11959 : (cuts11959.take 3).map (fun c => (1571422209-1+2*2^9*c.k,93279889354588+c.lower,93280265255700+c.upper)) = pointBounds11959 := by
 decide +kernel
def cuts11960 : List PrefixCut := [⟨25,218507749,218507915⟩,
⟨73,625423985,625424469⟩,
⟨121,1033402070,1033402867⟩,
⟨128,1096621416,1096622261⟩]
theorem checked11960 : checkPrefixCuts (2^48) 1571553281 9 Manual.Count131072.C011960.packed 128 cuts11960 = true := by
 decide +kernel
def pointBounds11960 : List (Nat × Nat × Nat) := [(1571578880,93281217471460,93281593373595),(1571628032,93281624387696,93282000290149),(1571677184,93282032365781,93282408268547)]
theorem point_links_checked11960 : (cuts11960.take 3).map (fun c => (1571553281-1+2*2^9*c.k,93280998963711+c.lower,93281374865680+c.upper)) = pointBounds11960 := by
 decide +kernel
def cuts11961 : List PrefixCut := [⟨41,343671531,343671796⟩,
⟨89,752519474,752520054⟩,
⟨128,1093664122,1093664962⟩]
theorem checked11961 : checkPrefixCuts (2^48) 1571684353 9 Manual.Count131072.C011961.packed 128 cuts11961 = true := by
 decide +kernel
def pointBounds11961 : List (Nat × Nat × Nat) := [(1571726336,93282439256658,93282815159737),(1571775488,93282848104601,93283224007995)]
theorem point_links_checked11961 : (cuts11961.take 2).map (fun c => (1571684353-1+2*2^9*c.k,93282095585127+c.lower,93282471487941+c.upper)) = pointBounds11961 := by
 decide +kernel
def cuts11962 : List PrefixCut := [⟨9,81121318,81121381⟩,
⟨57,496032159,496032541⟩,
⟨105,916839200,916839901⟩,
⟨128,1116315028,1116315880⟩]
theorem checked11962 : checkPrefixCuts (2^48) 1571815425 9 Manual.Count131072.C011962.packed 128 cuts11962 = true := by
 decide +kernel
def pointBounds11962 : List (Nat × Nat × Nat) := [(1571824640,93283270370567,93283646274284),(1571873792,93283685281408,93284061185444),(1571922944,93284106088449,93284481992804)]
theorem point_links_checked11962 : (cuts11962.take 3).map (fun c => (1571815425-1+2*2^9*c.k,93283189249249+c.lower,93283565152903+c.upper)) = pointBounds11962 := by
 decide +kernel
def cuts11963 : List PrefixCut := [⟨25,227943238,227943415⟩,
⟨73,641561733,641562229⟩,
⟨121,1057853037,1057853851⟩,
⟨128,1117296589,1117297448⟩]
theorem checked11963 : checkPrefixCuts (2^48) 1571946497 9 Manual.Count131072.C011963.packed 128 cuts11963 = true := by
 decide +kernel
def pointBounds11963 : List (Nat × Nat × Nat) := [(1571972096,93284533507515,93284909412198),(1572021248,93284947126010,93285323031012),(1572070400,93285363417314,93285739322634)]
theorem point_links_checked11963 : (cuts11963.take 3).map (fun c => (1571946497-1+2*2^9*c.k,93284305564277+c.lower,93284681468783+c.upper)) = pointBounds11963 := by
 decide +kernel
def cuts11964 : List PrefixCut := [⟨41,352000516,352000783⟩,
⟨89,761999496,762000077⟩,
⟨128,1111831461,1111832311⟩]
theorem checked11964 : checkPrefixCuts (2^48) 1572077569 9 Manual.Count131072.C011964.packed 128 cuts11964 = true := by
 decide +kernel
def pointBounds11964 : List (Nat × Nat × Nat) := [(1572119552,93285774861382,93286150767014),(1572168704,93286184860362,93286560766308)]
theorem point_links_checked11964 : (cuts11964.take 2).map (fun c => (1572077569-1+2*2^9*c.k,93285422860866+c.lower,93285798766231+c.upper)) = pointBounds11964 := by
 decide +kernel
def cuts11965 : List PrefixCut := [⟨9,77162351,77162411⟩,
⟨57,492864648,492865029⟩,
⟨105,909091013,909091707⟩,
⟨128,1106905845,1106906690⟩]
theorem checked11965 : checkPrefixCuts (2^48) 1572208641 9 Manual.Count131072.C011965.packed 128 cuts11965 = true := by
 decide +kernel
def pointBounds11965 : List (Nat × Nat × Nat) := [(1572217856,93286611854678,93286987760953),(1572267008,93287027556975,93287403463571),(1572316160,93287443783340,93287819690249)]
theorem point_links_checked11965 : (cuts11965.take 3).map (fun c => (1572208641-1+2*2^9*c.k,93286534692327+c.lower,93286910598542+c.upper)) = pointBounds11965 := by
 decide +kernel
def cuts11966 : List PrefixCut := [⟨25,212848942,212849108⟩,
⟨73,628512172,628512658⟩,
⟨121,1040582248,1040583050⟩,
⟨128,1099652931,1099653777⟩]
theorem checked11966 : checkPrefixCuts (2^48) 1572339713 9 Manual.Count131072.C011966.packed 128 cuts11966 = true := by
 decide +kernel
def pointBounds11966 : List (Nat × Nat × Nat) := [(1572365312,93287854447114,93288230354340),(1572414464,93288270110344,93288646017890),(1572463616,93288682180420,93289058088282)]
theorem point_links_checked11966 : (cuts11966.take 3).map (fun c => (1572339713-1+2*2^9*c.k,93287641598172+c.lower,93288017505232+c.upper)) = pointBounds11966 := by
 decide +kernel
def cuts11967 : List PrefixCut := [⟨41,353344544,353344814⟩,
⟨89,774338501,774339092⟩,
⟨128,1112090783,1112091634⟩]
theorem checked11967 : checkPrefixCuts (2^48) 1572470785 9 Manual.Count131072.C011967.packed 128 cuts11967 = true := by
 decide +kernel
def pointBounds11967 : List (Nat × Nat × Nat) := [(1572512768,93289094595647,93289470503823),(1572561920,93289515589604,93289891498101)]
theorem point_links_checked11967 : (cuts11967.take 2).map (fun c => (1572470785-1+2*2^9*c.k,93288741251103+c.lower,93289117159009+c.upper)) = pointBounds11967 := by
 decide +kernel
def cuts11968 : List PrefixCut := [⟨9,78037990,78038048⟩,
⟨57,494352225,494352605⟩,
⟨105,904210245,904210944⟩,
⟨128,1102691473,1102692324⟩]
theorem checked11968 : checkPrefixCuts (2^48) 1572601857 9 Manual.Count131072.C011968.packed 128 cuts11968 = true := by
 decide +kernel
def pointBounds11968 : List (Nat × Nat × Nat) := [(1572611072,93289931379876,93290307288691),(1572660224,93290347694111,93290723603248),(1572709376,93290757552131,93291133461587)]
theorem point_links_checked11968 : (cuts11968.take 3).map (fun c => (1572601857-1+2*2^9*c.k,93289853341886+c.lower,93290229250643+c.upper)) = pointBounds11968 := by
 decide +kernel
def cuts11969 : List PrefixCut := [⟨25,222639133,222639302⟩,
⟨73,622628352,622628831⟩,
⟨121,1033700627,1033701425⟩,
⟨128,1095082981,1095083827⟩]
theorem checked11969 : checkPrefixCuts (2^48) 1572732929 9 Manual.Count131072.C011969.packed 128 cuts11969 = true := by
 decide +kernel
def pointBounds11969 : List (Nat × Nat × Nat) := [(1572758528,93291178672492,93291554582269),(1572807680,93291578661711,93291954571798),(1572856832,93291989733986,93292365644392)]
theorem point_links_checked11969 : (cuts11969.take 3).map (fun c => (1572732929-1+2*2^9*c.k,93290956033359+c.lower,93291331942967+c.upper)) = pointBounds11969 := by
 decide +kernel
def cuts11970 : List PrefixCut := [⟨41,356298409,356298682⟩,
⟨90,783271337,783271940⟩,
⟨128,1115033882,1115034737⟩]
theorem checked11970 : checkPrefixCuts (2^48) 1572864001 9 Manual.Count131072.C011970.packed 128 cuts11970 = true := by
 decide +kernel
def pointBounds11970 : List (Nat × Nat × Nat) := [(1572905984,93292407414749,93292783325476),(1572956160,93292834387677,93293210298734)]
theorem point_links_checked11970 : (cuts11970.take 2).map (fun c => (1572864001-1+2*2^9*c.k,93292051116340+c.lower,93292427026794+c.upper)) = pointBounds11970 := by
 decide +kernel
def cuts11971 : List PrefixCut := [⟨11,94838921,94838994⟩,
⟨60,518384844,518385242⟩,
⟨109,944959038,944959758⟩,
⟨128,1109215106,1109215953⟩]
theorem checked11971 : checkPrefixCuts (2^48) 1572995073 9 Manual.Count131072.C011971.packed 128 cuts11971 = true := by
 decide +kernel
def pointBounds11971 : List (Nat × Nat × Nat) := [(1573006336,93293260989143,93293636900525),(1573056512,93293684535066,93294060446773),(1573106688,93294111109260,93294487021289)]
theorem point_links_checked11971 : (cuts11971.take 3).map (fun c => (1572995073-1+2*2^9*c.k,93293166150222+c.lower,93293542061531+c.upper)) = pointBounds11971 := by
 decide +kernel
def cuts11972 : List PrefixCut := [⟨30,260515277,260515474⟩,
⟨79,678831899,678832418⟩,
⟨128,1099103369,1099104214⟩]
theorem checked11972 : checkPrefixCuts (2^48) 1573126145 9 Manual.Count131072.C011972.packed 128 cuts11972 = true := by
 decide +kernel
def pointBounds11972 : List (Nat × Nat × Nat) := [(1573156864,93294535880605,93294911792958),(1573207040,93294954197227,93295330109902),(1573257216,93295374468697,93295750381698)]
theorem point_links_checked11972 : (cuts11972.take 3).map (fun c => (1573126145-1+2*2^9*c.k,93294275365328+c.lower,93294651277484+c.upper)) = pointBounds11972 := by
 decide +kernel
def cuts11973 : List PrefixCut := [⟨49,419363459,419363778⟩,
⟨98,852846899,852847547⟩,
⟨128,1123700013,1123700867⟩]
theorem checked11973 : checkPrefixCuts (2^48) 1573257217 9 Manual.Count131072.C011973.packed 128 cuts11973 = true := by
 decide +kernel
def pointBounds11973 : List (Nat × Nat × Nat) := [(1573307392,93295793832156,93296169745476),(1573357568,93296227315596,93296603229245)]
theorem point_links_checked11973 : (cuts11973.take 2).map (fun c => (1573257217-1+2*2^9*c.k,93295374468697+c.lower,93295750381698+c.upper)) = pointBounds11973 := by
 decide +kernel
def cuts11974 : List PrefixCut := [⟨19,159575371,159575492⟩,
⟨68,575678637,575679079⟩,
⟨117,1001965186,1001965955⟩,
⟨128,1098562008,1098562853⟩]
theorem checked11974 : checkPrefixCuts (2^48) 1573388289 9 Manual.Count131072.C011974.packed 128 cuts11974 = true := by
 decide +kernel
def pointBounds11974 : List (Nat × Nat × Nat) := [(1573407744,93296657744081,93297033658057),(1573457920,93297073847347,93297449761644),(1573508096,93297500133896,93297876048520)]
theorem point_links_checked11974 : (cuts11974.take 3).map (fun c => (1573388289-1+2*2^9*c.k,93296498168710+c.lower,93296874082565+c.upper)) = pointBounds11974 := by
 decide +kernel
def cuts11975 : List PrefixCut := [⟨38,326456258,326456511⟩,
⟨87,746991634,746992209⟩,
⟨128,1103300402,1103301249⟩]
theorem checked11975 : checkPrefixCuts (2^48) 1573519361 9 Manual.Count131072.C011975.packed 128 cuts11975 = true := by
 decide +kernel
def pointBounds11975 : List (Nat × Nat × Nat) := [(1573558272,93297923186976,93298299101929),(1573608448,93298343722352,93298719637627)]
theorem point_links_checked11975 : (cuts11975.take 2).map (fun c => (1573519361-1+2*2^9*c.k,93297596730718+c.lower,93297972645418+c.upper)) = pointBounds11975 := by
 decide +kernel
def cuts11976 : List PrefixCut := [⟨8,72977737,72977794⟩,
⟨57,492591883,492592259⟩,
⟨106,909867622,909868321⟩,
⟨128,1100525826,1100526674⟩]
theorem checked11976 : checkPrefixCuts (2^48) 1573650433 9 Manual.Count131072.C011976.packed 128 cuts11976 = true := by
 decide +kernel
def pointBounds11976 : List (Nat × Nat × Nat) := [(1573658624,93298773008857,93299148924461),(1573708800,93299192623003,93299568538926),(1573758976,93299609898742,93299985814988)]
theorem point_links_checked11976 : (cuts11976.take 3).map (fun c => (1573650433-1+2*2^9*c.k,93298700031120+c.lower,93299075946667+c.upper)) = pointBounds11976 := by
 decide +kernel
def cuts11977 : List PrefixCut := [⟨27,240375748,240375928⟩,
⟨76,666746021,666746528⟩,
⟨125,1084518337,1084519166⟩,
⟨128,1109734474,1109735322⟩]
theorem checked11977 : checkPrefixCuts (2^48) 1573781505 9 Manual.Count131072.C011977.packed 128 cuts11977 = true := by
 decide +kernel
def pointBounds11977 : List (Nat × Nat × Nat) := [(1573809152,93300040932694,93300416849269),(1573859328,93300467302967,93300843219869),(1573909504,93300885075283,93301260992507)]
theorem point_links_checked11977 : (cuts11977.take 3).map (fun c => (1573781505-1+2*2^9*c.k,93299800556946+c.lower,93300176473341+c.upper)) = pointBounds11977 := by
 decide +kernel
def cuts11978 : List PrefixCut := [⟨46,386820107,386820404⟩,
⟨95,808678822,808679437⟩,
⟨128,1093546587,1093547422⟩]
theorem checked11978 : checkPrefixCuts (2^48) 1573912577 9 Manual.Count131072.C011978.packed 128 cuts11978 = true := by
 decide +kernel
def pointBounds11978 : List (Nat × Nat × Nat) := [(1573959680,93301297111527,93301673029067),(1574009856,93301718970242,93302094888100)]
theorem point_links_checked11978 : (cuts11978.take 2).map (fun c => (1573912577-1+2*2^9*c.k,93300910291420+c.lower,93301286208663+c.upper)) = pointBounds11978 := by
 decide +kernel
def cuts11979 : List PrefixCut := [⟨16,133222260,133222362⟩,
⟨65,554875373,554875799⟩,
⟨114,991892823,991893582⟩,
⟨128,1109370164,1109371013⟩]
theorem checked11979 : checkPrefixCuts (2^48) 1574043649 9 Manual.Count131072.C011979.packed 128 cuts11979 = true := by
 decide +kernel
def pointBounds11979 : List (Nat × Nat × Nat) := [(1574060032,93302137060267,93302512978447),(1574110208,93302558713380,93302934631884),(1574160384,93302995730830,93303371649667)]
theorem point_links_checked11979 : (cuts11979.take 3).map (fun c => (1574043649-1+2*2^9*c.k,93302003838007+c.lower,93302379756085+c.upper)) = pointBounds11979 := by
 decide +kernel
def cuts11980 : List PrefixCut := [⟨35,297354147,297354372⟩,
⟨84,722900550,722901102⟩,
⟨128,1114462839,1114463691⟩]
theorem checked11980 : checkPrefixCuts (2^48) 1574174721 9 Manual.Count131072.C011980.packed 128 cuts11980 = true := by
 decide +kernel
def pointBounds11980 : List (Nat × Nat × Nat) := [(1574210560,93303410562318,93303786481470),(1574260736,93303836108721,93304212028200)]
theorem point_links_checked11980 : (cuts11980.take 2).map (fun c => (1574174721-1+2*2^9*c.k,93303113208171+c.lower,93303489127098+c.upper)) = pointBounds11980 := by
 decide +kernel
def cuts11981 : List PrefixCut := [⟨5,44698180,44698213⟩,
⟨54,470038578,470038938⟩,
⟨103,894292644,894293325⟩,
⟨128,1102749615,1102750455⟩]
theorem checked11981 : checkPrefixCuts (2^48) 1574305793 9 Manual.Count131072.C011981.packed 128 cuts11981 = true := by
 decide +kernel
def pointBounds11981 : List (Nat × Nat × Nat) := [(1574310912,93304272369190,93304648289002),(1574361088,93304697709588,93305073629727),(1574411264,93305121963654,93305497884114)]
theorem point_links_checked11981 : (cuts11981.take 3).map (fun c => (1574305793-1+2*2^9*c.k,93304227671010+c.lower,93304603590789+c.upper)) = pointBounds11981 := by
 decide +kernel
def cuts11982 : List PrefixCut := [⟨24,202196455,202196613⟩,
⟨73,626244846,626245334⟩,
⟨122,1058860398,1058861221⟩,
⟨128,1113740815,1113741678⟩]
theorem checked11982 : checkPrefixCuts (2^48) 1574436865 9 Manual.Count131072.C011982.packed 128 cuts11982 = true := by
 decide +kernel
def pointBounds11982 : List (Nat × Nat × Nat) := [(1574461440,93305532617080,93305908537857),(1574511616,93305956665471,93306332586578),(1574561792,93306389281023,93306765202465)]
theorem point_links_checked11982 : (cuts11982.take 3).map (fun c => (1574436865-1+2*2^9*c.k,93305330420625+c.lower,93305706341244+c.upper)) = pointBounds11982 := by
 decide +kernel
def cuts11983 : List PrefixCut := [⟨43,372001096,372001380⟩,
⟨92,798869032,798869637⟩,
⟨128,1105426030,1105426870⟩]
theorem checked11983 : checkPrefixCuts (2^48) 1574567937 9 Manual.Count131072.C011983.packed 128 cuts11983 = true := by
 decide +kernel
def pointBounds11983 : List (Nat × Nat × Nat) := [(1574611968,93306816162536,93307192084302),(1574662144,93307243030472,93307618952559)]
theorem point_links_checked11983 : (cuts11983.take 2).map (fun c => (1574567937-1+2*2^9*c.k,93306444161440+c.lower,93306820082922+c.upper)) = pointBounds11983 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000061
