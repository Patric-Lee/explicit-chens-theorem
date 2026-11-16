import PlattAssemblyKernel
import PlattCertificates.Count131072.C019728
import PlattCertificates.Count131072.C019729
import PlattCertificates.Count131072.C019730
import PlattCertificates.Count131072.C019731
import PlattCertificates.Count131072.C019732
import PlattCertificates.Count131072.C019733
import PlattCertificates.Count131072.C019734
import PlattCertificates.Count131072.C019735
import PlattCertificates.Count131072.C019736
import PlattCertificates.Count131072.C019737
import PlattCertificates.Count131072.C019738
import PlattCertificates.Count131072.C019739
import PlattCertificates.Count131072.C019740
import PlattCertificates.Count131072.C019741
import PlattCertificates.Count131072.C019742
import PlattCertificates.Count131072.C019743
import PlattCertificates.Count131072.C019744
import PlattCertificates.Count131072.C019745
import PlattCertificates.Count131072.C019746
import PlattCertificates.Count131072.C019747
import PlattCertificates.Count131072.C019748
import PlattCertificates.Count131072.C019749
import PlattCertificates.Count131072.C019750
import PlattCertificates.Count131072.C019751
import PlattCertificates.Count131072.C019752
import PlattCertificates.Count131072.C019753
import PlattCertificates.Count131072.C019754
import PlattCertificates.Count131072.C019755
import PlattCertificates.Count131072.C019756
import PlattCertificates.Count131072.C019757
import PlattCertificates.Count131072.C019758
import PlattCertificates.Count131072.C019759
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000304
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19728 : List PrefixCut := [⟨61,305087183,305087364⟩,
⟨128,650488833,650489217⟩]
theorem checked19728 : checkPrefixCuts (2^48) 2589720577 9 Manual.Count131072.C019728.packed 128 cuts19728 = true := by
 decide +kernel
def pointBounds19728 : List (Nat × Nat × Nat) := [(2589783040,99843697384556,99844077649990)]
theorem point_links_checked19728 : (cuts19728.take 1).map (fun c => (2589720577-1+2*2^9*c.k,99843392297373+c.lower,99843772562626+c.upper)) = pointBounds19728 := by
 decide +kernel
def cuts19729 : List PrefixCut := [⟨13,69340079,69340120⟩,
⟨93,483960001,483960286⟩,
⟨128,665345340,665345733⟩]
theorem checked19729 : checkPrefixCuts (2^48) 2589851649 9 Manual.Count131072.C019729.packed 128 cuts19729 = true := by
 decide +kernel
def pointBounds19729 : List (Nat × Nat × Nat) := [(2589864960,99844112126285,99844492391963),(2589946880,99844526746207,99844907012129)]
theorem point_links_checked19729 : (cuts19729.take 2).map (fun c => (2589851649-1+2*2^9*c.k,99844042786206+c.lower,99844423051843+c.upper)) = pointBounds19729 := by
 decide +kernel
def cuts19730 : List PrefixCut := [⟨45,232026104,232026238⟩,
⟨125,643033625,643034000⟩,
⟨128,659117208,659117592⟩]
theorem checked19730 : checkPrefixCuts (2^48) 2589982721 9 Manual.Count131072.C019730.packed 128 cuts19730 = true := by
 decide +kernel
def pointBounds19730 : List (Nat × Nat × Nat) := [(2590028800,99844940157650,99845320423814),(2590110720,99845351165171,99845731431576)]
theorem point_links_checked19730 : (cuts19730.take 2).map (fun c => (2589982721-1+2*2^9*c.k,99844708131546+c.lower,99845088397576+c.upper)) = pointBounds19730 := by
 decide +kernel
def cuts19731 : List PrefixCut := [⟨77,399366430,399366666⟩,
⟨128,664951977,664952366⟩]
theorem checked19731 : checkPrefixCuts (2^48) 2590113793 9 Manual.Count131072.C019731.packed 128 cuts19731 = true := by
 decide +kernel
def pointBounds19731 : List (Nat × Nat × Nat) := [(2590192640,99845766615184,99846146881834)]
theorem point_links_checked19731 : (cuts19731.take 1).map (fun c => (2590113793-1+2*2^9*c.k,99845367248754+c.lower,99845747515168+c.upper)) = pointBounds19731 := by
 decide +kernel
def cuts19732 : List PrefixCut := [⟨29,152567991,152568080⟩,
⟨109,559189954,559190289⟩,
⟨128,659267841,659268235⟩]
theorem checked19732 : checkPrefixCuts (2^48) 2590244865 9 Manual.Count131072.C019732.packed 128 cuts19732 = true := by
 decide +kernel
def pointBounds19732 : List (Nat × Nat × Nat) := [(2590274560,99846184768722,99846565035614),(2590356480,99846591390685,99846971657823)]
theorem point_links_checked19732 : (cuts19732.take 2).map (fun c => (2590244865-1+2*2^9*c.k,99846032200731+c.lower,99846412467534+c.upper)) = pointBounds19732 := by
 decide +kernel
def cuts19733 : List PrefixCut := [⟨61,313268168,313268357⟩,
⟨128,660755639,660756030⟩]
theorem checked19733 : checkPrefixCuts (2^48) 2590375937 9 Manual.Count131072.C019733.packed 128 cuts19733 = true := by
 decide +kernel
def pointBounds19733 : List (Nat × Nat × Nat) := [(2590438400,99847004736740,99847385004126)]
theorem point_links_checked19733 : (cuts19733.take 1).map (fun c => (2590375937-1+2*2^9*c.k,99846691468572+c.lower,99847071735769+c.upper)) = pointBounds19733 := by
 decide +kernel
def cuts19734 : List PrefixCut := [⟨13,68670607,68670646⟩,
⟨93,483620217,483620504⟩,
⟨128,659853015,659853408⟩]
theorem checked19734 : checkPrefixCuts (2^48) 2590507009 9 Manual.Count131072.C019734.packed 128 cuts19734 = true := by
 decide +kernel
def pointBounds19734 : List (Nat × Nat × Nat) := [(2590520320,99847420894818,99847801162445),(2590602240,99847835844428,99848216112303)]
theorem point_links_checked19734 : (cuts19734.take 2).map (fun c => (2590507009-1+2*2^9*c.k,99847352224211+c.lower,99847732491799+c.upper)) = pointBounds19734 := by
 decide +kernel
def cuts19735 : List PrefixCut := [⟨45,229685754,229685887⟩,
⟨125,641023784,641024161⟩,
⟨128,656234135,656234521⟩]
theorem checked19735 : checkPrefixCuts (2^48) 2590638081 9 Manual.Count131072.C019735.packed 128 cuts19735 = true := by
 decide +kernel
def pointBounds19735 : List (Nat × Nat × Nat) := [(2590684160,99848241762980,99848622031094),(2590766080,99848653101010,99849033369368)]
theorem point_links_checked19735 : (cuts19735.take 2).map (fun c => (2590638081-1+2*2^9*c.k,99848012077226+c.lower,99848392345207+c.upper)) = pointBounds19735 := by
 decide +kernel
def cuts19736 : List PrefixCut := [⟨77,393181371,393181608⟩,
⟨128,656961481,656961872⟩]
theorem checked19736 : checkPrefixCuts (2^48) 2590769153 9 Manual.Count131072.C019736.packed 128 cuts19736 = true := by
 decide +kernel
def pointBounds19736 : List (Nat × Nat × Nat) := [(2590848000,99849061492732,99849441761336)]
theorem point_links_checked19736 : (cuts19736.take 1).map (fun c => (2590769153-1+2*2^9*c.k,99848668311361+c.lower,99849048579728+c.upper)) = pointBounds19736 := by
 decide +kernel
def cuts19737 : List PrefixCut := [⟨29,148401140,148401228⟩,
⟨109,558287992,558288324⟩,
⟨128,654212455,654212845⟩]
theorem checked19737 : checkPrefixCuts (2^48) 2590900225 9 Manual.Count131072.C019737.packed 128 cuts19737 = true := by
 decide +kernel
def pointBounds19737 : List (Nat × Nat × Nat) := [(2590929920,99849473673982,99849853942828),(2591011840,99849883560834,99850263829924)]
theorem point_links_checked19737 : (cuts19737.take 2).map (fun c => (2590900225-1+2*2^9*c.k,99849325272842+c.lower,99849705541600+c.upper)) = pointBounds19737 := by
 decide +kernel
def cuts19738 : List PrefixCut := [⟨61,308191804,308191988⟩,
⟨128,651246189,651246578⟩]
theorem checked19738 : checkPrefixCuts (2^48) 2591031297 9 Manual.Count131072.C019738.packed 128 cuts19738 = true := by
 decide +kernel
def pointBounds19738 : List (Nat × Nat × Nat) := [(2591093760,99850287677101,99850667946433)]
theorem point_links_checked19738 : (cuts19738.take 1).map (fun c => (2591031297-1+2*2^9*c.k,99849979485297+c.lower,99850359754445+c.upper)) = pointBounds19738 := by
 decide +kernel
def cuts19739 : List PrefixCut := [⟨13,65720266,65720304⟩,
⟨93,480890899,480891185⟩,
⟨128,659794736,659795127⟩]
theorem checked19739 : checkPrefixCuts (2^48) 2591162369 9 Manual.Count131072.C019739.packed 128 cuts19739 = true := by
 decide +kernel
def pointBounds19739 : List (Nat × Nat × Nat) := [(2591175680,99850696451752,99851076721327),(2591257600,99851111622385,99851491892208)]
theorem point_links_checked19739 : (cuts19739.take 2).map (fun c => (2591162369-1+2*2^9*c.k,99850630731486+c.lower,99851011001023+c.upper)) = pointBounds19739 := by
 decide +kernel
def cuts19740 : List PrefixCut := [⟨45,233320796,233320932⟩,
⟨125,646509995,646510371⟩,
⟨128,663345768,663346153⟩]
theorem checked19740 : checkPrefixCuts (2^48) 2591293441 9 Manual.Count131072.C019740.packed 128 cuts19740 = true := by
 decide +kernel
def pointBounds19740 : List (Nat × Nat × Nat) := [(2591339520,99851523847018,99851904117082),(2591421440,99851937036217,99852317306521)]
theorem point_links_checked19740 : (cuts19740.take 2).map (fun c => (2591293441-1+2*2^9*c.k,99851290526222+c.lower,99851670796150+c.upper)) = pointBounds19740 := by
 decide +kernel
def cuts19741 : List PrefixCut := [⟨77,398512812,398513047⟩,
⟨128,659945273,659945661⟩]
theorem checked19741 : checkPrefixCuts (2^48) 2591424513 9 Manual.Count131072.C019741.packed 128 cuts19741 = true := by
 decide +kernel
def pointBounds19741 : List (Nat × Nat × Nat) := [(2591503360,99852352384802,99852732655350)]
theorem point_links_checked19741 : (cuts19741.take 1).map (fun c => (2591424513-1+2*2^9*c.k,99851953871990+c.lower,99852334142303+c.upper)) = pointBounds19741 := by
 decide +kernel
def cuts19742 : List PrefixCut := [⟨29,146408597,146408679⟩,
⟨109,561079215,561079539⟩,
⟨128,659260165,659260548⟩]
theorem checked19742 : checkPrefixCuts (2^48) 2591555585 9 Manual.Count131072.C019742.packed 128 cuts19742 = true := by
 decide +kernel
def pointBounds19742 : List (Nat × Nat × Nat) := [(2591585280,99852760225860,99853140496643),(2591667200,99853174896478,99853555167503)]
theorem point_links_checked19742 : (cuts19742.take 2).map (fun c => (2591555585-1+2*2^9*c.k,99852613817263+c.lower,99852994087964+c.upper)) = pointBounds19742 := by
 decide +kernel
def cuts19743 : List PrefixCut := [⟨61,314195784,314195965⟩,
⟨128,660530026,660530408⟩]
theorem checked19743 : checkPrefixCuts (2^48) 2591686657 9 Manual.Count131072.C019743.packed 128 cuts19743 = true := by
 decide +kernel
def pointBounds19743 : List (Nat × Nat × Nat) := [(2591749120,99853587273212,99853967544477)]
theorem point_links_checked19743 : (cuts19743.take 1).map (fun c => (2591686657-1+2*2^9*c.k,99853273077428+c.lower,99853653348512+c.upper)) = pointBounds19743 := by
 decide +kernel
def cuts19744 : List PrefixCut := [⟨13,66246645,66246682⟩,
⟨93,472407221,472407496⟩,
⟨128,654523738,654524119⟩]
theorem checked19744 : checkPrefixCuts (2^48) 2591817729 9 Manual.Count131072.C019744.packed 128 cuts19744 = true := by
 decide +kernel
def pointBounds19744 : List (Nat × Nat × Nat) := [(2591831040,99853999854099,99854380125602),(2591912960,99854406014675,99854786286416)]
theorem point_links_checked19744 : (cuts19744.take 2).map (fun c => (2591817729-1+2*2^9*c.k,99853933607454+c.lower,99854313878920+c.upper)) = pointBounds19744 := by
 decide +kernel
def cuts19745 : List PrefixCut := [⟨45,229460989,229461125⟩,
⟨125,638962241,638962615⟩,
⟨128,655467986,655468370⟩]
theorem checked19745 : checkPrefixCuts (2^48) 2591948801 9 Manual.Count131072.C019745.packed 128 cuts19745 = true := by
 decide +kernel
def pointBounds19745 : List (Nat × Nat × Nat) := [(2591994880,99854817592181,99855197864164),(2592076800,99855227093433,99855607365654)]
theorem point_links_checked19745 : (cuts19745.take 2).map (fun c => (2591948801-1+2*2^9*c.k,99854588131192+c.lower,99854968403039+c.upper)) = pointBounds19745 := by
 decide +kernel
def cuts19746 : List PrefixCut := [⟨77,399389306,399389541⟩,
⟨128,655543577,655543967⟩]
theorem checked19746 : checkPrefixCuts (2^48) 2592079873 9 Manual.Count131072.C019746.packed 128 cuts19746 = true := by
 decide +kernel
def pointBounds19746 : List (Nat × Nat × Nat) := [(2592158720,99855642988484,99856023260950)]
theorem point_links_checked19746 : (cuts19746.take 1).map (fun c => (2592079873-1+2*2^9*c.k,99855243599178+c.lower,99855623871409+c.upper)) = pointBounds19746 := by
 decide +kernel
def cuts19747 : List PrefixCut := [⟨29,149846272,149846361⟩,
⟨109,561045942,561046274⟩,
⟨128,656921895,656922281⟩]
theorem checked19747 : checkPrefixCuts (2^48) 2592210945 9 Manual.Count131072.C019747.packed 128 cuts19747 = true := by
 decide +kernel
def pointBounds19747 : List (Nat × Nat × Nat) := [(2592240640,99856048989027,99856429261737),(2592322560,99856460188697,99856840461650)]
theorem point_links_checked19747 : (cuts19747.take 2).map (fun c => (2592210945-1+2*2^9*c.k,99855899142755+c.lower,99856279415376+c.upper)) = pointBounds19747 := by
 decide +kernel
def cuts19748 : List PrefixCut := [⟨61,311293303,311293486⟩,
⟨128,652219870,652220256⟩]
theorem checked19748 : checkPrefixCuts (2^48) 2592342017 9 Manual.Count131072.C019748.packed 128 cuts19748 = true := by
 decide +kernel
def pointBounds19748 : List (Nat × Nat × Nat) := [(2592404480,99856867357953,99857247631143)]
theorem point_links_checked19748 : (cuts19748.take 1).map (fun c => (2592342017-1+2*2^9*c.k,99856556064650+c.lower,99856936337657+c.upper)) = pointBounds19748 := by
 decide +kernel
def cuts19749 : List PrefixCut := [⟨13,71441441,71441481⟩,
⟨93,479236507,479236783⟩,
⟨128,661849829,661850212⟩]
theorem checked19749 : checkPrefixCuts (2^48) 2592473089 9 Manual.Count131072.C019749.packed 128 cuts19749 = true := by
 decide +kernel
def pointBounds19749 : List (Nat × Nat × Nat) := [(2592486400,99857279725961,99857659999394),(2592568320,99857687521027,99858067794696)]
theorem point_links_checked19749 : (cuts19749.take 2).map (fun c => (2592473089-1+2*2^9*c.k,99857208284520+c.lower,99857588557913+c.upper)) = pointBounds19749 := by
 decide +kernel
def cuts19750 : List PrefixCut := [⟨45,233962850,233962989⟩,
⟨125,644229120,644229496⟩,
⟨128,657799492,657799877⟩]
theorem checked19750 : checkPrefixCuts (2^48) 2592604161 9 Manual.Count131072.C019750.packed 128 cuts19750 = true := by
 decide +kernel
def pointBounds19750 : List (Nat × Nat × Nat) := [(2592650240,99858104097199,99858484371114),(2592732160,99858514363469,99858894637621)]
theorem point_links_checked19750 : (cuts19750.take 2).map (fun c => (2592604161-1+2*2^9*c.k,99857870134349+c.lower,99858250408125+c.upper)) = pointBounds19750 := by
 decide +kernel
def cuts19751 : List PrefixCut := [⟨77,392448946,392449178⟩,
⟨128,654943417,654943808⟩]
theorem checked19751 : checkPrefixCuts (2^48) 2592735233 9 Manual.Count131072.C019751.packed 128 cuts19751 = true := by
 decide +kernel
def pointBounds19751 : List (Nat × Nat × Nat) := [(2592814080,99858920382787,99859300657180)]
theorem point_links_checked19751 : (cuts19751.take 1).map (fun c => (2592735233-1+2*2^9*c.k,99858527933841+c.lower,99858908208002+c.upper)) = pointBounds19751 := by
 decide +kernel
def cuts19752 : List PrefixCut := [⟨29,147637240,147637327⟩,
⟨109,559492947,559493281⟩,
⟨128,657407163,657407556⟩]
theorem checked19752 : checkPrefixCuts (2^48) 2592866305 9 Manual.Count131072.C019752.packed 128 cuts19752 = true := by
 decide +kernel
def pointBounds19752 : List (Nat × Nat × Nat) := [(2592896000,99859330514498,99859710789137),(2592977920,99859742370205,99860122645091)]
theorem point_links_checked19752 : (cuts19752.take 2).map (fun c => (2592866305-1+2*2^9*c.k,99859182877258+c.lower,99859563151810+c.upper)) = pointBounds19752 := by
 decide +kernel
def cuts19753 : List PrefixCut := [⟨61,312734373,312734561⟩,
⟨128,658133755,658134148⟩]
theorem checked19753 : checkPrefixCuts (2^48) 2592997377 9 Manual.Count131072.C019753.packed 128 cuts19753 = true := by
 decide +kernel
def pointBounds19753 : List (Nat × Nat × Nat) := [(2593059840,99860153018794,99860533293927)]
theorem point_links_checked19753 : (cuts19753.take 1).map (fun c => (2592997377-1+2*2^9*c.k,99859840284421+c.lower,99860220559366+c.upper)) = pointBounds19753 := by
 decide +kernel
def cuts19754 : List PrefixCut := [⟨13,68709732,68709770⟩,
⟨93,473905180,473905457⟩,
⟨128,652999033,652999417⟩]
theorem checked19754 : checkPrefixCuts (2^48) 2593128449 9 Manual.Count131072.C019754.packed 128 cuts19754 = true := by
 decide +kernel
def pointBounds19754 : List (Nat × Nat × Nat) := [(2593141760,99860567127908,99860947403284),(2593223680,99860972323356,99861352598971)]
theorem point_links_checked19754 : (cuts19754.take 2).map (fun c => (2593128449-1+2*2^9*c.k,99860498418176+c.lower,99860878693514+c.upper)) = pointBounds19754 := by
 decide +kernel
def cuts19755 : List PrefixCut := [⟨45,230213324,230213461⟩,
⟨125,638747835,638748213⟩,
⟨128,654268418,654268804⟩]
theorem checked19755 : checkPrefixCuts (2^48) 2593259521 9 Manual.Count131072.C019755.packed 128 cuts19755 = true := by
 decide +kernel
def pointBounds19755 : List (Nat × Nat × Nat) := [(2593305600,99861381630533,99861761906392),(2593387520,99861790165044,99862170441144)]
theorem point_links_checked19755 : (cuts19755.take 2).map (fun c => (2593259521-1+2*2^9*c.k,99861151417209+c.lower,99861531692931+c.upper)) = pointBounds19755 := by
 decide +kernel
def cuts19756 : List PrefixCut := [⟨77,395280224,395280462⟩,
⟨128,657382831,657383228⟩]
theorem checked19756 : checkPrefixCuts (2^48) 2593390593 9 Manual.Count131072.C019756.packed 128 cuts19756 = true := by
 decide +kernel
def pointBounds19756 : List (Nat × Nat × Nat) := [(2593469440,99862200965851,99862581242197)]
theorem point_links_checked19756 : (cuts19756.take 1).map (fun c => (2593390593-1+2*2^9*c.k,99861805685627+c.lower,99862185961735+c.upper)) = pointBounds19756 := by
 decide +kernel
def cuts19757 : List PrefixCut := [⟨29,143801434,143801519⟩,
⟨109,548173107,548173431⟩,
⟨128,644543235,644543614⟩]
theorem checked19757 : checkPrefixCuts (2^48) 2593521665 9 Manual.Count131072.C019757.packed 128 cuts19757 = true := by
 decide +kernel
def pointBounds19757 : List (Nat × Nat × Nat) := [(2593551360,99862606869892,99862987146482),(2593633280,99863011241565,99863391518394)]
theorem point_links_checked19757 : (cuts19757.take 2).map (fun c => (2593521665-1+2*2^9*c.k,99862463068458+c.lower,99862843344963+c.upper)) = pointBounds19757 := by
 decide +kernel
def cuts19758 : List PrefixCut := [⟨61,318624165,318624352⟩,
⟨128,658618780,658619171⟩]
theorem checked19758 : checkPrefixCuts (2^48) 2593652737 9 Manual.Count131072.C019758.packed 128 cuts19758 = true := by
 decide +kernel
def pointBounds19758 : List (Nat × Nat × Nat) := [(2593715200,99863426235858,99863806512929)]
theorem point_links_checked19758 : (cuts19758.take 1).map (fun c => (2593652737-1+2*2^9*c.k,99863107611693+c.lower,99863487888577+c.upper)) = pointBounds19758 := by
 decide +kernel
def cuts19759 : List PrefixCut := [⟨13,67824215,67824255⟩,
⟨93,471723572,471723852⟩,
⟨128,651640264,651640647⟩]
theorem checked19759 : checkPrefixCuts (2^48) 2593783809 9 Manual.Count131072.C019759.packed 128 cuts19759 = true := by
 decide +kernel
def pointBounds19759 : List (Nat × Nat × Nat) := [(2593797120,99863834054688,99864214332003),(2593879040,99864237954045,99864618231600)]
theorem point_links_checked19759 : (cuts19759.take 2).map (fun c => (2593783809-1+2*2^9*c.k,99863766230473+c.lower,99864146507748+c.upper)) = pointBounds19759 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000304
