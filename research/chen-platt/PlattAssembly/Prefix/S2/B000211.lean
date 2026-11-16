import PlattAssemblyKernel
import PlattCertificates.Count131072.C016752
import PlattCertificates.Count131072.C016753
import PlattCertificates.Count131072.C016754
import PlattCertificates.Count131072.C016755
import PlattCertificates.Count131072.C016756
import PlattCertificates.Count131072.C016757
import PlattCertificates.Count131072.C016758
import PlattCertificates.Count131072.C016759
import PlattCertificates.Count131072.C016760
import PlattCertificates.Count131072.C016761
import PlattCertificates.Count131072.C016762
import PlattCertificates.Count131072.C016763
import PlattCertificates.Count131072.C016764
import PlattCertificates.Count131072.C016765
import PlattCertificates.Count131072.C016766
import PlattCertificates.Count131072.C016767
import PlattCertificates.Count131072.C016768
import PlattCertificates.Count131072.C016769
import PlattCertificates.Count131072.C016770
import PlattCertificates.Count131072.C016771
import PlattCertificates.Count131072.C016772
import PlattCertificates.Count131072.C016773
import PlattCertificates.Count131072.C016774
import PlattCertificates.Count131072.C016775
import PlattCertificates.Count131072.C016776
import PlattCertificates.Count131072.C016777
import PlattCertificates.Count131072.C016778
import PlattCertificates.Count131072.C016779
import PlattCertificates.Count131072.C016780
import PlattCertificates.Count131072.C016781
import PlattCertificates.Count131072.C016782
import PlattCertificates.Count131072.C016783
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000211
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16752 : List PrefixCut := [⟨36,214209081,214209217⟩,
⟨104,620351827,620352217⟩,
⟨128,766350272,766350751⟩]
theorem checked16752 : checkPrefixCuts (2^48) 2199650305 9 Manual.Count131072.C016752.packed 128 cuts16752 = true := by
 decide +kernel
def pointBounds16752 : List (Nat × Nat × Nat) := [(2199687168,97715444266537,97715823236579),(2199756800,97715850409283,97716229379579)]
theorem point_links_checked16752 : (cuts16752.take 2).map (fun c => (2199650305-1+2*2^9*c.k,97715230057456+c.lower,97715609027362+c.upper)) = pointBounds16752 := by
 decide +kernel
def cuts16753 : List PrefixCut := [⟨44,269728165,269728337⟩,
⟨112,679555845,679556281⟩,
⟨128,779227881,779228379⟩]
theorem checked16753 : checkPrefixCuts (2^48) 2199781377 9 Manual.Count131072.C016753.packed 128 cuts16753 = true := by
 decide +kernel
def pointBounds16753 : List (Nat × Nat × Nat) := [(2199826432,97716266135893,97716645106450),(2199896064,97716675963573,97717054934394)]
theorem point_links_checked16753 : (cuts16753.take 2).map (fun c => (2199781377-1+2*2^9*c.k,97715996407728+c.lower,97716375378113+c.upper)) = pointBounds16753 := by
 decide +kernel
def cuts16754 : List PrefixCut := [⟨52,319227009,319227216⟩,
⟨120,733506731,733507196⟩,
⟨128,780461019,780461515⟩]
theorem checked16754 : checkPrefixCuts (2^48) 2199912449 9 Manual.Count131072.C016754.packed 128 cuts16754 = true := by
 decide +kernel
def pointBounds16754 : List (Nat × Nat × Nat) := [(2199965696,97717094862618,97717473833708),(2200035328,97717509142340,97717888113688)]
theorem point_links_checked16754 : (cuts16754.take 2).map (fun c => (2199912449-1+2*2^9*c.k,97716775635609+c.lower,97717154606492+c.upper)) = pointBounds16754 := by
 decide +kernel
def cuts16755 : List PrefixCut := [⟨60,364369731,364369958⟩,
⟨128,783356838,783357329⟩]
theorem checked16755 : checkPrefixCuts (2^48) 2200043521 9 Manual.Count131072.C016755.packed 128 cuts16755 = true := by
 decide +kernel
def pointBounds16755 : List (Nat × Nat × Nat) := [(2200104960,97717920466359,97718299437965),(2200174592,97718339453466,97718718425336)]
theorem point_links_checked16755 : (cuts16755.take 2).map (fun c => (2200043521-1+2*2^9*c.k,97717556096628+c.lower,97717935068007+c.upper)) = pointBounds16755 := by
 decide +kernel
def cuts16756 : List PrefixCut := [⟨68,415008093,415008350⟩,
⟨128,785613076,785613565⟩]
theorem checked16756 : checkPrefixCuts (2^48) 2200174593 9 Manual.Count131072.C016756.packed 128 cuts16756 = true := by
 decide +kernel
def pointBounds16756 : List (Nat × Nat × Nat) := [(2200244224,97718754461559,97719133433686)]
theorem point_links_checked16756 : (cuts16756.take 1).map (fun c => (2200174593-1+2*2^9*c.k,97718339453466+c.lower,97718718425336+c.upper)) = pointBounds16756 := by
 decide +kernel
def cuts16757 : List PrefixCut := [⟨8,47716070,47716100⟩,
⟨76,461802437,461802730⟩,
⟨128,774437177,774437664⟩]
theorem checked16757 : checkPrefixCuts (2^48) 2200305665 9 Manual.Count131072.C016757.packed 128 cuts16757 = true := by
 decide +kernel
def pointBounds16757 : List (Nat × Nat × Nat) := [(2200313856,97719172782612,97719551755001),(2200383488,97719586868979,97719965841631)]
theorem point_links_checked16757 : (cuts16757.take 2).map (fun c => (2200305665-1+2*2^9*c.k,97719125066542+c.lower,97719504038901+c.upper)) = pointBounds16757 := by
 decide +kernel
def cuts16758 : List PrefixCut := [⟨16,99775460,99775524⟩,
⟨84,509486422,509486744⟩,
⟨128,775158435,775158924⟩]
theorem checked16758 : checkPrefixCuts (2^48) 2200436737 9 Manual.Count131072.C016758.packed 128 cuts16758 = true := by
 decide +kernel
def pointBounds16758 : List (Nat × Nat × Nat) := [(2200453120,97719999279179,97720378252089),(2200522752,97720408990141,97720787963309)]
theorem point_links_checked16758 : (cuts16758.take 2).map (fun c => (2200436737-1+2*2^9*c.k,97719899503719+c.lower,97720278476565+c.upper)) = pointBounds16758 := by
 decide +kernel
def cuts16759 : List PrefixCut := [⟨24,141851526,141851617⟩,
⟨92,554222621,554222966⟩,
⟨128,771147062,771147541⟩]
theorem checked16759 : checkPrefixCuts (2^48) 2200567809 9 Manual.Count131072.C016759.packed 128 cuts16759 = true := by
 decide +kernel
def pointBounds16759 : List (Nat × Nat × Nat) := [(2200592384,97720816513680,97721195487106),(2200662016,97721228884775,97721607858455)]
theorem point_links_checked16759 : (cuts16759.take 2).map (fun c => (2200567809-1+2*2^9*c.k,97720674662154+c.lower,97721053635489+c.upper)) = pointBounds16759 := by
 decide +kernel
def cuts16760 : List PrefixCut := [⟨32,200165940,200166066⟩,
⟨100,614813110,614813499⟩,
⟨128,786577048,786577545⟩]
theorem checked16760 : checkPrefixCuts (2^48) 2200698881 9 Manual.Count131072.C016760.packed 128 cuts16760 = true := by
 decide +kernel
def pointBounds16760 : List (Nat × Nat × Nat) := [(2200731648,97721645975156,97722024949096),(2200801280,97722060622326,97722439596529)]
theorem point_links_checked16760 : (cuts16760.take 2).map (fun c => (2200698881-1+2*2^9*c.k,97721445809216+c.lower,97721824783030+c.upper)) = pointBounds16760 := by
 decide +kernel
def cuts16761 : List PrefixCut := [⟨40,246579039,246579195⟩,
⟨108,657874798,657875216⟩,
⟨128,782437570,782438066⟩]
theorem checked16761 : checkPrefixCuts (2^48) 2200829953 9 Manual.Count131072.C016761.packed 128 cuts16761 = true := by
 decide +kernel
def pointBounds16761 : List (Nat × Nat × Nat) := [(2200870912,97722478965303,97722857939770),(2200940544,97722890261062,97723269235791)]
theorem point_links_checked16761 : (cuts16761.take 2).map (fun c => (2200829953-1+2*2^9*c.k,97722232386264+c.lower,97722611360575+c.upper)) = pointBounds16761 := by
 decide +kernel
def cuts16762 : List PrefixCut := [⟨48,292986440,292986626⟩,
⟨116,707836910,707837356⟩,
⟨128,780728515,780729006⟩]
theorem checked16762 : checkPrefixCuts (2^48) 2200961025 9 Manual.Count131072.C016762.packed 128 cuts16762 = true := by
 decide +kernel
def pointBounds16762 : List (Nat × Nat × Nat) := [(2201010176,97723307810274,97723686785267),(2201079808,97723722660744,97724101635997)]
theorem point_links_checked16762 : (cuts16762.take 2).map (fun c => (2200961025-1+2*2^9*c.k,97723014823834+c.lower,97723393798641+c.upper)) = pointBounds16762 := by
 decide +kernel
def cuts16763 : List PrefixCut := [⟨56,330053093,330053302⟩,
⟨124,742191901,742192373⟩,
⟨128,767510588,767511077⟩]
theorem checked16763 : checkPrefixCuts (2^48) 2201092097 9 Manual.Count131072.C016763.packed 128 cuts16763 = true := by
 decide +kernel
def pointBounds16763 : List (Nat × Nat × Nat) := [(2201149440,97724125605442,97724504580949),(2201219072,97724537744250,97724916720020)]
theorem point_links_checked16763 : (cuts16763.take 2).map (fun c => (2201092097-1+2*2^9*c.k,97723795552349+c.lower,97724174527647+c.upper)) = pointBounds16763 := by
 decide +kernel
def cuts16764 : List PrefixCut := [⟨64,392305539,392305785⟩,
⟨128,779356902,779357385⟩]
theorem checked16764 : checkPrefixCuts (2^48) 2201223169 9 Manual.Count131072.C016764.packed 128 cuts16764 = true := by
 decide +kernel
def pointBounds16764 : List (Nat × Nat × Nat) := [(2201288704,97724955368476,97725334344509)]
theorem point_links_checked16764 : (cuts16764.take 1).map (fun c => (2201223169-1+2*2^9*c.k,97724563062937+c.lower,97724942038724+c.upper)) = pointBounds16764 := by
 decide +kernel
def cuts16765 : List PrefixCut := [⟨4,24933540,24933555⟩,
⟨72,439334823,439335098⟩,
⟨128,782634773,782635263⟩]
theorem checked16765 : checkPrefixCuts (2^48) 2201354241 9 Manual.Count131072.C016765.packed 128 cuts16765 = true := by
 decide +kernel
def pointBounds16765 : List (Nat × Nat × Nat) := [(2201358336,97725367353379,97725746329664),(2201427968,97725781754662,97726160731207)]
theorem point_links_checked16765 : (cuts16765.take 2).map (fun c => (2201354241-1+2*2^9*c.k,97725342419839+c.lower,97725721396109+c.upper)) = pointBounds16765 := by
 decide +kernel
def cuts16766 : List PrefixCut := [⟨12,77608872,77608919⟩,
⟨80,487892674,487892980⟩,
⟨128,779392145,779392633⟩]
theorem checked16766 : checkPrefixCuts (2^48) 2201485313 9 Manual.Count131072.C016766.packed 128 cuts16766 = true := by
 decide +kernel
def pointBounds16766 : List (Nat × Nat × Nat) := [(2201497600,97726202663484,97726581640291),(2201567232,97726612947286,97726991924352)]
theorem point_links_checked16766 : (cuts16766.take 2).map (fun c => (2201485313-1+2*2^9*c.k,97726125054612+c.lower,97726504031372+c.upper)) = pointBounds16766 := by
 decide +kernel
def cuts16767 : List PrefixCut := [⟨20,120305528,120305602⟩,
⟨88,530179711,530180043⟩,
⟨128,774103717,774104205⟩]
theorem checked16767 : checkPrefixCuts (2^48) 2201616385 9 Manual.Count131072.C016767.packed 128 cuts16767 = true := by
 decide +kernel
def pointBounds16767 : List (Nat × Nat × Nat) := [(2201636864,97727024752285,97727403729607),(2201706496,97727434626468,97727813604048)]
theorem point_links_checked16767 : (cuts16767.take 2).map (fun c => (2201616385-1+2*2^9*c.k,97726904446757+c.lower,97727283424005+c.upper)) = pointBounds16767 := by
 decide +kernel
def cuts16768 : List PrefixCut := [⟨28,165553766,165553870⟩,
⟨96,579492898,579493261⟩,
⟨128,781088602,781089087⟩]
theorem checked16768 : checkPrefixCuts (2^48) 2201747457 9 Manual.Count131072.C016768.packed 128 cuts16768 = true := by
 decide +kernel
def pointBounds16768 : List (Nat × Nat × Nat) := [(2201776128,97727844104240,97728223082080),(2201845760,97728258043372,97728637021471)]
theorem point_links_checked16768 : (cuts16768.take 2).map (fun c => (2201747457-1+2*2^9*c.k,97727678550474+c.lower,97728057528210+c.upper)) = pointBounds16768 := by
 decide +kernel
def cuts16769 : List PrefixCut := [⟨36,220895241,220895378⟩,
⟨104,639154468,639154870⟩,
⟨128,782832116,782832609⟩]
theorem checked16769 : checkPrefixCuts (2^48) 2201878529 9 Manual.Count131072.C016769.packed 128 cuts16769 = true := by
 decide +kernel
def pointBounds16769 : List (Nat × Nat × Nat) := [(2201915392,97728680534317,97729059512675),(2201985024,97729098793544,97729477772167)]
theorem point_links_checked16769 : (cuts16769.take 2).map (fun c => (2201878529-1+2*2^9*c.k,97728459639076+c.lower,97728838617297+c.upper)) = pointBounds16769 := by
 decide +kernel
def cuts16770 : List PrefixCut := [⟨44,266387471,266387636⟩,
⟨112,673627590,673628006⟩,
⟨128,772304026,772304506⟩]
theorem checked16770 : checkPrefixCuts (2^48) 2202009601 9 Manual.Count131072.C016770.packed 128 cuts16770 = true := by
 decide +kernel
def pointBounds16770 : List (Nat × Nat × Nat) := [(2202054656,97729508858663,97729887837542),(2202124288,97729916098782,97730295077912)]
theorem point_links_checked16770 : (cuts16770.take 2).map (fun c => (2202009601-1+2*2^9*c.k,97729242471192+c.lower,97729621449906+c.upper)) = pointBounds16770 := by
 decide +kernel
def cuts16771 : List PrefixCut := [⟨52,316475373,316475577⟩,
⟨120,724839982,724840446⟩,
⟨128,774558610,774559102⟩]
theorem checked16771 : checkPrefixCuts (2^48) 2202140673 9 Manual.Count131072.C016771.packed 128 cuts16771 = true := by
 decide +kernel
def pointBounds16771 : List (Nat × Nat × Nat) := [(2202193920,97730331250591,97730710229989),(2202263552,97730739615200,97731118594858)]
theorem point_links_checked16771 : (cuts16771.take 2).map (fun c => (2202140673-1+2*2^9*c.k,97730014775218+c.lower,97730393754412+c.upper)) = pointBounds16771 := by
 decide +kernel
def cuts16772 : List PrefixCut := [⟨60,359655552,359655781⟩,
⟨128,773106616,773107105⟩]
theorem checked16772 : checkPrefixCuts (2^48) 2202271745 9 Manual.Count131072.C016772.packed 128 cuts16772 = true := by
 decide +kernel
def pointBounds16772 : List (Nat × Nat × Nat) := [(2202333184,97731148989380,97731527969295),(2202402816,97731562440444,97731941420619)]
theorem point_links_checked16772 : (cuts16772.take 2).map (fun c => (2202271745-1+2*2^9*c.k,97730789333828+c.lower,97731168313514+c.upper)) = pointBounds16772 := by
 decide +kernel
def cuts16773 : List PrefixCut := [⟨68,414332649,414332907⟩,
⟨128,775489000,775489484⟩]
theorem checked16773 : checkPrefixCuts (2^48) 2202402817 9 Manual.Count131072.C016773.packed 128 cuts16773 = true := by
 decide +kernel
def pointBounds16773 : List (Nat × Nat × Nat) := [(2202472448,97731976773093,97732355753526)]
theorem point_links_checked16773 : (cuts16773.take 1).map (fun c => (2202402817-1+2*2^9*c.k,97731562440444+c.lower,97731941420619+c.upper)) = pointBounds16773 := by
 decide +kernel
def cuts16774 : List PrefixCut := [⟨8,46134249,46134278⟩,
⟨76,462868670,462868962⟩,
⟨128,770075530,770076019⟩]
theorem checked16774 : checkPrefixCuts (2^48) 2202533889 9 Manual.Count131072.C016774.packed 128 cuts16774 = true := by
 decide +kernel
def pointBounds16774 : List (Nat × Nat × Nat) := [(2202542080,97732384063693,97732763044381),(2202611712,97732800798114,97733179779065)]
theorem point_links_checked16774 : (cuts16774.take 2).map (fun c => (2202533889-1+2*2^9*c.k,97732337929444+c.lower,97732716910103+c.upper)) = pointBounds16774 := by
 decide +kernel
def cuts16775 : List PrefixCut := [⟨16,97757710,97757771⟩,
⟨84,499898229,499898544⟩,
⟨128,763895906,763896385⟩]
theorem checked16775 : checkPrefixCuts (2^48) 2202664961 9 Manual.Count131072.C016775.packed 128 cuts16775 = true := by
 decide +kernel
def pointBounds16775 : List (Nat × Nat × Nat) := [(2202681344,97733205762684,97733584743893),(2202750976,97733607903203,97733986884666)]
theorem point_links_checked16775 : (cuts16775.take 2).map (fun c => (2202664961-1+2*2^9*c.k,97733108004974+c.lower,97733486986122+c.upper)) = pointBounds16775 := by
 decide +kernel
def cuts16776 : List PrefixCut := [⟨24,148097048,148097139⟩,
⟨92,564523175,564523520⟩,
⟨128,778672721,778673203⟩]
theorem checked16776 : checkPrefixCuts (2^48) 2202796033 9 Manual.Count131072.C016776.packed 128 cuts16776 = true := by
 decide +kernel
def pointBounds16776 : List (Nat × Nat × Nat) := [(2202820608,97734019997928,97734398979646),(2202890240,97734436424055,97734815406027)]
theorem point_links_checked16776 : (cuts16776.take 2).map (fun c => (2202796033-1+2*2^9*c.k,97733871900880+c.lower,97734250882507+c.upper)) = pointBounds16776 := by
 decide +kernel
def cuts16777 : List PrefixCut := [⟨32,198174645,198174771⟩,
⟨100,613807879,613808265⟩,
⟨128,785398102,785398595⟩]
theorem checked16777 : checkPrefixCuts (2^48) 2202927105 9 Manual.Count131072.C016777.packed 128 cuts16777 = true := by
 decide +kernel
def pointBounds16777 : List (Nat × Nat × Nat) := [(2202959872,97734848748246,97735227730481),(2203029504,97735264381480,97735643363975)]
theorem point_links_checked16777 : (cuts16777.take 2).map (fun c => (2202927105-1+2*2^9*c.k,97734650573601+c.lower,97735029555710+c.upper)) = pointBounds16777 := by
 decide +kernel
def cuts16778 : List PrefixCut := [⟨40,242880007,242880161⟩,
⟨108,664363998,664364414⟩,
⟨128,789056313,789056806⟩]
theorem checked16778 : checkPrefixCuts (2^48) 2203058177 9 Manual.Count131072.C016778.packed 128 cuts16778 = true := by
 decide +kernel
def pointBounds16778 : List (Nat × Nat × Nat) := [(2203099136,97735678851710,97736057834466),(2203168768,97736100335701,97736479318719)]
theorem point_links_checked16778 : (cuts16778.take 2).map (fun c => (2203058177-1+2*2^9*c.k,97735435971703+c.lower,97735814954305+c.upper)) = pointBounds16778 := by
 decide +kernel
def cuts16779 : List PrefixCut := [⟨48,292306869,292307053⟩,
⟨116,702777469,702777906⟩,
⟨128,777511620,777512105⟩]
theorem checked16779 : checkPrefixCuts (2^48) 2203189249 9 Manual.Count131072.C016779.packed 128 cuts16779 = true := by
 decide +kernel
def pointBounds16779 : List (Nat × Nat × Nat) := [(2203238400,97736517334885,97736896318164),(2203308032,97736927805485,97737306789017)]
theorem point_links_checked16779 : (cuts16779.take 2).map (fun c => (2203189249-1+2*2^9*c.k,97736225028016+c.lower,97736604011111+c.upper)) = pointBounds16779 := by
 decide +kernel
def cuts16780 : List PrefixCut := [⟨56,331763296,331763505⟩,
⟨124,744762916,744763383⟩,
⟨128,769289543,769290026⟩]
theorem checked16780 : checkPrefixCuts (2^48) 2203320321 9 Manual.Count131072.C016780.packed 128 cuts16780 = true := by
 decide +kernel
def pointBounds16780 : List (Nat × Nat × Nat) := [(2203377664,97737334302932,97737713286721),(2203447296,97737747302552,97738126286599)]
theorem point_links_checked16780 : (cuts16780.take 2).map (fun c => (2203320321-1+2*2^9*c.k,97737002539636+c.lower,97737381523216+c.upper)) = pointBounds16780 := by
 decide +kernel
def cuts16781 : List PrefixCut := [⟨64,381050943,381051179⟩,
⟨128,771543055,771543534⟩]
theorem checked16781 : checkPrefixCuts (2^48) 2203451393 9 Manual.Count131072.C016781.packed 128 cuts16781 = true := by
 decide +kernel
def pointBounds16781 : List (Nat × Nat × Nat) := [(2203516928,97738152880122,97738531864421)]
theorem point_links_checked16781 : (cuts16781.take 1).map (fun c => (2203451393-1+2*2^9*c.k,97737771829179+c.lower,97738150813242+c.upper)) = pointBounds16781 := by
 decide +kernel
def cuts16782 : List PrefixCut := [⟨4,24908327,24908343⟩,
⟨72,437102223,437102495⟩,
⟨128,775840066,775840548⟩]
theorem checked16782 : checkPrefixCuts (2^48) 2203582465 9 Manual.Count131072.C016782.packed 128 cuts16782 = true := by
 decide +kernel
def pointBounds16782 : List (Nat × Nat × Nat) := [(2203586560,97738568280561,97738947265119),(2203656192,97738980474457,97739359459271)]
theorem point_links_checked16782 : (cuts16782.take 2).map (fun c => (2203582465-1+2*2^9*c.k,97738543372234+c.lower,97738922356776+c.upper)) = pointBounds16782 := by
 decide +kernel
def cuts16783 : List PrefixCut := [⟨12,74337215,74337264⟩,
⟨80,483567508,483567810⟩,
⟨128,772473203,772473691⟩]
theorem checked16783 : checkPrefixCuts (2^48) 2203713537 9 Manual.Count131072.C016783.packed 128 cuts16783 = true := by
 decide +kernel
def pointBounds16783 : List (Nat × Nat × Nat) := [(2203725824,97739393549515,97739772534588),(2203795456,97739802779808,97740181765134)]
theorem point_links_checked16783 : (cuts16783.take 2).map (fun c => (2203713537-1+2*2^9*c.k,97739319212300+c.lower,97739698197324+c.upper)) = pointBounds16783 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000211
