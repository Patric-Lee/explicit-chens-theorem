import PlattAssemblyKernel
import PlattCertificates.Count131072.C020768
import PlattCertificates.Count131072.C020769
import PlattCertificates.Count131072.C020770
import PlattCertificates.Count131072.C020771
import PlattCertificates.Count131072.C020772
import PlattCertificates.Count131072.C020773
import PlattCertificates.Count131072.C020774
import PlattCertificates.Count131072.C020775
import PlattCertificates.Count131072.C020776
import PlattCertificates.Count131072.C020777
import PlattCertificates.Count131072.C020778
import PlattCertificates.Count131072.C020779
import PlattCertificates.Count131072.C020780
import PlattCertificates.Count131072.C020781
import PlattCertificates.Count131072.C020782
import PlattCertificates.Count131072.C020783
import PlattCertificates.Count131072.C020784
import PlattCertificates.Count131072.C020785
import PlattCertificates.Count131072.C020786
import PlattCertificates.Count131072.C020787
import PlattCertificates.Count131072.C020788
import PlattCertificates.Count131072.C020789
import PlattCertificates.Count131072.C020790
import PlattCertificates.Count131072.C020791
import PlattCertificates.Count131072.C020792
import PlattCertificates.Count131072.C020793
import PlattCertificates.Count131072.C020794
import PlattCertificates.Count131072.C020795
import PlattCertificates.Count131072.C020796
import PlattCertificates.Count131072.C020797
import PlattCertificates.Count131072.C020798
import PlattCertificates.Count131072.C020799
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000024
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20768 : List PrefixCut := [⟨45,216315962,216316093⟩,
⟨128,626531987,626532361⟩]
theorem checked20768 : checkPrefixCuts (2^48) 2726035457 9 Manual.Count131072.C020768.packed 128 cuts20768 = true := by
 decide +kernel
def pointBounds20768 : List (Nat × Nat × Nat) := [(2726081536,100508936530556,100509317185545)]
theorem point_links_checked20768 : (cuts20768.take 1).map (fun c => (2726035457-1+2*2^9*c.k,100508720214594+c.lower,100509100869452+c.upper)) = pointBounds20768 := by
 decide +kernel
def cuts20769 : List PrefixCut := [⟨1,4749469,4749472⟩,
⟨85,417327143,417327384⟩,
⟨128,629909015,629909381⟩]
theorem checked20769 : checkPrefixCuts (2^48) 2726166529 9 Manual.Count131072.C020769.packed 128 cuts20769 = true := by
 decide +kernel
def pointBounds20769 : List (Nat × Nat × Nat) := [(2726167552,100509351496050,100509732151285),(2726253568,100509764073724,100510144729197)]
theorem point_links_checked20769 : (cuts20769.take 2).map (fun c => (2726166529-1+2*2^9*c.k,100509346746581+c.lower,100509727401813+c.upper)) = pointBounds20769 := by
 decide +kernel
def cuts20770 : List PrefixCut := [⟨41,193891451,193891565⟩,
⟨125,603862089,603862438⟩,
⟨128,617799417,617799775⟩]
theorem checked20770 : checkPrefixCuts (2^48) 2726297601 9 Manual.Count131072.C020770.packed 128 cuts20770 = true := by
 decide +kernel
def pointBounds20770 : List (Nat × Nat × Nat) := [(2726339584,100510170547047,100510551202759),(2726425600,100510580517685,100510961173632)]
theorem point_links_checked20770 : (cuts20770.take 2).map (fun c => (2726297601-1+2*2^9*c.k,100509976655596+c.lower,100510357311194+c.upper)) = pointBounds20770 := by
 decide +kernel
def cuts20771 : List PrefixCut := [⟨81,390135828,390136058⟩,
⟨128,620970117,620970480⟩]
theorem checked20771 : checkPrefixCuts (2^48) 2726428673 9 Manual.Count131072.C020771.packed 128 cuts20771 = true := by
 decide +kernel
def pointBounds20771 : List (Nat × Nat × Nat) := [(2726511616,100510984590841,100511365247027)]
theorem point_links_checked20771 : (cuts20771.take 1).map (fun c => (2726428673-1+2*2^9*c.k,100510594455013+c.lower,100510975110969+c.upper)) = pointBounds20771 := by
 decide +kernel
def cuts20772 : List PrefixCut := [⟨37,179729918,179730022⟩,
⟨121,589145598,589145938⟩,
⟨128,621662930,621663290⟩]
theorem checked20772 : checkPrefixCuts (2^48) 2726559745 9 Manual.Count131072.C020772.packed 128 cuts20772 = true := by
 decide +kernel
def pointBounds20772 : List (Nat × Nat × Nat) := [(2726597632,100511395155048,100511775811471),(2726683648,100511804570728,100512185227387)]
theorem point_links_checked20772 : (cuts20772.take 2).map (fun c => (2726559745-1+2*2^9*c.k,100511215425130+c.lower,100511596081449+c.upper)) = pointBounds20772 := by
 decide +kernel
def cuts20773 : List PrefixCut := [⟨77,371930430,371930646⟩,
⟨128,619258758,619259119⟩]
theorem checked20773 : checkPrefixCuts (2^48) 2726690817 9 Manual.Count131072.C020773.packed 128 cuts20773 = true := by
 decide +kernel
def pointBounds20773 : List (Nat × Nat × Nat) := [(2726769664,100512209018490,100512589675385)]
theorem point_links_checked20773 : (cuts20773.take 1).map (fun c => (2726690817-1+2*2^9*c.k,100511837088060+c.lower,100512217744739+c.upper)) = pointBounds20773 := by
 decide +kernel
def cuts20774 : List PrefixCut := [⟨33,157726093,157726187⟩,
⟨117,564419317,564419646⟩,
⟨128,619229018,619229378⟩]
theorem checked20774 : checkPrefixCuts (2^48) 2726821889 9 Manual.Count131072.C020774.packed 128 cuts20774 = true := by
 decide +kernel
def pointBounds20774 : List (Nat × Nat × Nat) := [(2726855680,100512614072911,100512994730045),(2726941696,100513020766135,100513401423504)]
theorem point_links_checked20774 : (cuts20774.take 2).map (fun c => (2726821889-1+2*2^9*c.k,100512456346818+c.lower,100512837003858+c.upper)) = pointBounds20774 := by
 decide +kernel
def cuts20775 : List PrefixCut := [⟨73,345884020,345884223⟩,
⟨128,614554430,614554784⟩]
theorem checked20775 : checkPrefixCuts (2^48) 2726952961 9 Manual.Count131072.C020775.packed 128 cuts20775 = true := by
 decide +kernel
def pointBounds20775 : List (Nat × Nat × Nat) := [(2727027712,100513421459856,100513802117459)]
theorem point_links_checked20775 : (cuts20775.take 1).map (fun c => (2726952961-1+2*2^9*c.k,100513075575836+c.lower,100513456233236+c.upper)) = pointBounds20775 := by
 decide +kernel
def cuts20776 : List PrefixCut := [⟨29,144706069,144706156⟩,
⟨113,550947926,550948256⟩,
⟨128,621337099,621337471⟩]
theorem checked20776 : checkPrefixCuts (2^48) 2727084033 9 Manual.Count131072.C020776.packed 128 cuts20776 = true := by
 decide +kernel
def pointBounds20776 : List (Nat × Nat × Nat) := [(2727113728,100513834836335,100514215494176),(2727199744,100514241078192,100514621736276)]
theorem point_links_checked20776 : (cuts20776.take 2).map (fun c => (2727084033-1+2*2^9*c.k,100513690130266+c.lower,100514070788020+c.upper)) = pointBounds20776 := by
 decide +kernel
def cuts20777 : List PrefixCut := [⟨69,339348918,339349110⟩,
⟨128,623061783,623062136⟩]
theorem checked20777 : checkPrefixCuts (2^48) 2727215105 9 Manual.Count131072.C020777.packed 128 cuts20777 = true := by
 decide +kernel
def pointBounds20777 : List (Nat × Nat × Nat) := [(2727285760,100514650816283,100515031474601)]
theorem point_links_checked20777 : (cuts20777.take 1).map (fun c => (2727215105-1+2*2^9*c.k,100514311467365+c.lower,100514692125491+c.upper)) = pointBounds20777 := by
 decide +kernel
def cuts20778 : List PrefixCut := [⟨25,121780962,121781034⟩,
⟨109,528706680,528706990⟩,
⟨128,620038757,620039122⟩]
theorem checked20778 : checkPrefixCuts (2^48) 2727346177 9 Manual.Count131072.C020778.packed 128 cuts20778 = true := by
 decide +kernel
def pointBounds20778 : List (Nat × Nat × Nat) := [(2727371776,100515056310110,100515436968661),(2727457792,100515463235828,100515843894617)]
theorem point_links_checked20778 : (cuts20778.take 2).map (fun c => (2727346177-1+2*2^9*c.k,100514934529148+c.lower,100515315187627+c.upper)) = pointBounds20778 := by
 decide +kernel
def cuts20779 : List PrefixCut := [⟨65,314961699,314961880⟩,
⟨128,623517629,623517992⟩]
theorem checked20779 : checkPrefixCuts (2^48) 2727477249 9 Manual.Count131072.C020779.packed 128 cuts20779 = true := by
 decide +kernel
def pointBounds20779 : List (Nat × Nat × Nat) := [(2727543808,100515869529604,100516250188629)]
theorem point_links_checked20779 : (cuts20779.take 1).map (fun c => (2727477249-1+2*2^9*c.k,100515554567905+c.lower,100515935226749+c.upper)) = pointBounds20779 := by
 decide +kernel
def cuts20780 : List PrefixCut := [⟨21,104639086,104639145⟩,
⟨105,510804108,510804403⟩,
⟨128,624932522,624932884⟩]
theorem checked20780 : checkPrefixCuts (2^48) 2727608321 9 Manual.Count131072.C020780.packed 128 cuts20780 = true := by
 decide +kernel
def pointBounds20780 : List (Nat × Nat × Nat) := [(2727629824,100516282724620,100516663383886),(2727715840,100516688889642,100517069549144)]
theorem point_links_checked20780 : (cuts20780.take 2).map (fun c => (2727608321-1+2*2^9*c.k,100516178085534+c.lower,100516558744741+c.upper)) = pointBounds20780 := by
 decide +kernel
def cuts20781 : List PrefixCut := [⟨61,290166450,290166625⟩,
⟨128,616131471,616131838⟩]
theorem checked20781 : checkPrefixCuts (2^48) 2727739393 9 Manual.Count131072.C020781.packed 128 cuts20781 = true := by
 decide +kernel
def pointBounds20781 : List (Nat × Nat × Nat) := [(2727801856,100517093184506,100517473844250)]
theorem point_links_checked20781 : (cuts20781.take 1).map (fun c => (2727739393-1+2*2^9*c.k,100516803018056+c.lower,100517183677625+c.upper)) = pointBounds20781 := by
 decide +kernel
def cuts20782 : List PrefixCut := [⟨17,83373093,83373140⟩,
⟨101,481864124,481864403⟩,
⟨128,613935063,613935418⟩]
theorem checked20782 : checkPrefixCuts (2^48) 2727870465 9 Manual.Count131072.C020782.packed 128 cuts20782 = true := by
 decide +kernel
def pointBounds20782 : List (Nat × Nat × Nat) := [(2727887872,100517502522620,100517883182603),(2727973888,100517901013651,100518281673866)]
theorem point_links_checked20782 : (cuts20782.take 2).map (fun c => (2727870465-1+2*2^9*c.k,100517419149527+c.lower,100517799809463+c.upper)) = pointBounds20782 := by
 decide +kernel
def cuts20783 : List PrefixCut := [⟨57,279924012,279924174⟩,
⟨128,615762929,615763287⟩]
theorem checked20783 : checkPrefixCuts (2^48) 2728001537 9 Manual.Count131072.C020783.packed 128 cuts20783 = true := by
 decide +kernel
def pointBounds20783 : List (Nat × Nat × Nat) := [(2728059904,100518313008602,100518693669055)]
theorem point_links_checked20783 : (cuts20783.take 1).map (fun c => (2728001537-1+2*2^9*c.k,100518033084590+c.lower,100518413744881+c.upper)) = pointBounds20783 := by
 decide +kernel
def cuts20784 : List PrefixCut := [⟨13,62730206,62730243⟩,
⟨97,467064438,467064711⟩,
⟨128,614598351,614598712⟩]
theorem checked20784 : checkPrefixCuts (2^48) 2728132609 9 Manual.Count131072.C020784.packed 128 cuts20784 = true := by
 decide +kernel
def pointBounds20784 : List (Nat × Nat × Nat) := [(2728145920,100518711577725,100519092238411),(2728231936,100519115911957,100519496572879)]
theorem point_links_checked20784 : (cuts20784.take 2).map (fun c => (2728132609-1+2*2^9*c.k,100518648847519+c.lower,100519029508168+c.upper)) = pointBounds20784 := by
 decide +kernel
def cuts20785 : List PrefixCut := [⟨53,254517806,254517957⟩,
⟨128,616632106,616632463⟩]
theorem checked20785 : checkPrefixCuts (2^48) 2728263681 9 Manual.Count131072.C020785.packed 128 cuts20785 = true := by
 decide +kernel
def pointBounds20785 : List (Nat × Nat × Nat) := [(2728317952,100519517963676,100519898624837)]
theorem point_links_checked20785 : (cuts20785.take 1).map (fun c => (2728263681-1+2*2^9*c.k,100519263445870+c.lower,100519644106880+c.upper)) = pointBounds20785 := by
 decide +kernel
def cuts20786 : List PrefixCut := [⟨9,46011522,46011550⟩,
⟨93,460107942,460108209⟩,
⟨128,629807351,629807719⟩]
theorem checked20786 : checkPrefixCuts (2^48) 2728394753 9 Manual.Count131072.C020786.packed 128 cuts20786 = true := by
 decide +kernel
def pointBounds20786 : List (Nat × Nat × Nat) := [(2728403968,100519926089498,100520306750893),(2728489984,100520340185918,100520720847552)]
theorem point_links_checked20786 : (cuts20786.take 2).map (fun c => (2728394753-1+2*2^9*c.k,100519880077976+c.lower,100520260739343+c.upper)) = pointBounds20786 := by
 decide +kernel
def cuts20787 : List PrefixCut := [⟨49,244693386,244693524⟩,
⟨128,628951881,628952241⟩]
theorem checked20787 : checkPrefixCuts (2^48) 2728525825 9 Manual.Count131072.C020787.packed 128 cuts20787 = true := by
 decide +kernel
def pointBounds20787 : List (Nat × Nat × Nat) := [(2728576000,100520754578713,100521135240586)]
theorem point_links_checked20787 : (cuts20787.take 1).map (fun c => (2728525825-1+2*2^9*c.k,100520509885327+c.lower,100520890547062+c.upper)) = pointBounds20787 := by
 decide +kernel
def cuts20788 : List PrefixCut := [⟨5,24344582,24344596⟩,
⟨89,423857247,423857486⟩,
⟨128,614067511,614067863⟩]
theorem checked20788 : checkPrefixCuts (2^48) 2728656897 9 Manual.Count131072.C020788.packed 128 cuts20788 = true := by
 decide +kernel
def pointBounds20788 : List (Nat × Nat × Nat) := [(2728662016,100521163181790,100521543843899),(2728748032,100521562694455,100521943356789)]
theorem point_links_checked20788 : (cuts20788.take 2).map (fun c => (2728656897-1+2*2^9*c.k,100521138837208+c.lower,100521519499303+c.upper)) = pointBounds20788 := by
 decide +kernel
def cuts20789 : List PrefixCut := [⟨45,217541820,217541949⟩,
⟨128,623733919,623734283⟩]
theorem checked20789 : checkPrefixCuts (2^48) 2728787969 9 Manual.Count131072.C020789.packed 128 cuts20789 = true := by
 decide +kernel
def pointBounds20789 : List (Nat × Nat × Nat) := [(2728834048,100521970446539,100522351109115)]
theorem point_links_checked20789 : (cuts20789.take 1).map (fun c => (2728787969-1+2*2^9*c.k,100521752904719+c.lower,100522133567166+c.upper)) = pointBounds20789 := by
 decide +kernel
def cuts20790 : List PrefixCut := [⟨1,6188711,6188714⟩,
⟨85,413811928,413812167⟩,
⟨128,624425990,624426352⟩]
theorem checked20790 : checkPrefixCuts (2^48) 2728919041 9 Manual.Count131072.C020790.packed 128 cuts20790 = true := by
 decide +kernel
def pointBounds20790 : List (Nat × Nat × Nat) := [(2728920064,100522382827349,100522763490163),(2729006080,100522790450566,100523171113616)]
theorem point_links_checked20790 : (cuts20790.take 2).map (fun c => (2728919041-1+2*2^9*c.k,100522376638638+c.lower,100522757301449+c.upper)) = pointBounds20790 := by
 decide +kernel
def cuts20791 : List PrefixCut := [⟨41,204938087,204938206⟩,
⟨125,607688181,607688533⟩,
⟨128,622849078,622849439⟩]
theorem checked20791 : checkPrefixCuts (2^48) 2729050113 9 Manual.Count131072.C020791.packed 128 cuts20791 = true := by
 decide +kernel
def pointBounds20791 : List (Nat × Nat × Nat) := [(2729092096,100523206002715,100523586666007),(2729178112,100523608752809,100523989416334)]
theorem point_links_checked20791 : (cuts20791.take 2).map (fun c => (2729050113-1+2*2^9*c.k,100523001064628+c.lower,100523381727801+c.upper)) = pointBounds20791 := by
 decide +kernel
def cuts20792 : List PrefixCut := [⟨81,386854625,386854851⟩,
⟨128,613640231,613640591⟩]
theorem checked20792 : checkPrefixCuts (2^48) 2729181185 9 Manual.Count131072.C020792.packed 128 cuts20792 = true := by
 decide +kernel
def pointBounds20792 : List (Nat × Nat × Nat) := [(2729264128,100524010768331,100524391432091)]
theorem point_links_checked20792 : (cuts20792.take 1).map (fun c => (2729181185-1+2*2^9*c.k,100523623913706+c.lower,100524004577240+c.upper)) = pointBounds20792 := by
 decide +kernel
def cuts20793 : List PrefixCut := [⟨37,183158191,183158296⟩,
⟨121,598348667,598349008⟩,
⟨128,632895717,632896077⟩]
theorem checked20793 : checkPrefixCuts (2^48) 2729312257 9 Manual.Count131072.C020793.packed 128 cuts20793 = true := by
 decide +kernel
def pointBounds20793 : List (Nat × Nat × Nat) := [(2729350144,100524420712128,100524801376127),(2729436160,100524835902604,100525216566839)]
theorem point_links_checked20793 : (cuts20793.take 2).map (fun c => (2729312257-1+2*2^9*c.k,100524237553937+c.lower,100524618217831+c.upper)) = pointBounds20793 := by
 decide +kernel
def cuts20794 : List PrefixCut := [⟨77,373205382,373205603⟩,
⟨128,623068586,623068954⟩]
theorem checked20794 : checkPrefixCuts (2^48) 2729443329 9 Manual.Count131072.C020794.packed 128 cuts20794 = true := by
 decide +kernel
def pointBounds20794 : List (Nat × Nat × Nat) := [(2729522176,100525243655036,100525624319511)]
theorem point_links_checked20794 : (cuts20794.take 1).map (fun c => (2729443329-1+2*2^9*c.k,100524870449654+c.lower,100525251113908+c.upper)) = pointBounds20794 := by
 decide +kernel
def cuts20795 : List PrefixCut := [⟨33,158185768,158185860⟩,
⟨117,560756618,560756948⟩,
⟨128,614479896,614480256⟩]
theorem checked20795 : checkPrefixCuts (2^48) 2729574401 9 Manual.Count131072.C020795.packed 128 cuts20795 = true := by
 decide +kernel
def pointBounds20795 : List (Nat × Nat × Nat) := [(2729608192,100525651704008,100526032368722),(2729694208,100526054274858,100526434939810)]
theorem point_links_checked20795 : (cuts20795.take 2).map (fun c => (2729574401-1+2*2^9*c.k,100525493518240+c.lower,100525874182862+c.upper)) = pointBounds20795 := by
 decide +kernel
def cuts20796 : List PrefixCut := [⟨73,351618998,351619193⟩,
⟨128,620843374,620843722⟩]
theorem checked20796 : checkPrefixCuts (2^48) 2729705473 9 Manual.Count131072.C020796.packed 128 cuts20796 = true := by
 decide +kernel
def pointBounds20796 : List (Nat × Nat × Nat) := [(2729780224,100526459617134,100526840282311)]
theorem point_links_checked20796 : (cuts20796.take 1).map (fun c => (2729705473-1+2*2^9*c.k,100526107998136+c.lower,100526488663118+c.upper)) = pointBounds20796 := by
 decide +kernel
def cuts20797 : List PrefixCut := [⟨29,134970962,134971038⟩,
⟨113,543587184,543587499⟩,
⟨128,612152583,612152939⟩]
theorem checked20797 : checkPrefixCuts (2^48) 2729836545 9 Manual.Count131072.C020797.packed 128 cuts20797 = true := by
 decide +kernel
def pointBounds20797 : List (Nat × Nat × Nat) := [(2729866240,100526863812472,100527244477878),(2729952256,100527272428694,100527653094339)]
theorem point_links_checked20797 : (cuts20797.take 2).map (fun c => (2729836545-1+2*2^9*c.k,100526728841510+c.lower,100527109506840+c.upper)) = pointBounds20797 := by
 decide +kernel
def cuts20798 : List PrefixCut := [⟨69,335810534,335810727⟩,
⟨128,626969922,626970286⟩]
theorem checked20798 : checkPrefixCuts (2^48) 2729967617 9 Manual.Count131072.C020798.packed 128 cuts20798 = true := by
 decide +kernel
def pointBounds20798 : List (Nat × Nat × Nat) := [(2730038272,100527676804627,100528057470506)]
theorem point_links_checked20798 : (cuts20798.take 1).map (fun c => (2729967617-1+2*2^9*c.k,100527340994093+c.lower,100527721659779+c.upper)) = pointBounds20798 := by
 decide +kernel
def cuts20799 : List PrefixCut := [⟨25,120317866,120317938⟩,
⟨109,533328575,533328882⟩,
⟨128,622506660,622507021⟩]
theorem checked20799 : checkPrefixCuts (2^48) 2730098689 9 Manual.Count131072.C020799.packed 128 cuts20799 = true := by
 decide +kernel
def pointBounds20799 : List (Nat × Nat × Nat) := [(2730124288,100528088281881,100528468948003),(2730210304,100528501292590,100528881958947)]
theorem point_links_checked20799 : (cuts20799.take 2).map (fun c => (2730098689-1+2*2^9*c.k,100527967964015+c.lower,100528348630065+c.upper)) = pointBounds20799 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000024
