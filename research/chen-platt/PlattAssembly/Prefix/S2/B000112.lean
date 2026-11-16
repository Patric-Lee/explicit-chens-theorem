import PlattAssemblyKernel
import PlattCertificates.Count131072.C013584
import PlattCertificates.Count131072.C013585
import PlattCertificates.Count131072.C013586
import PlattCertificates.Count131072.C013587
import PlattCertificates.Count131072.C013588
import PlattCertificates.Count131072.C013589
import PlattCertificates.Count131072.C013590
import PlattCertificates.Count131072.C013591
import PlattCertificates.Count131072.C013592
import PlattCertificates.Count131072.C013593
import PlattCertificates.Count131072.C013594
import PlattCertificates.Count131072.C013595
import PlattCertificates.Count131072.C013596
import PlattCertificates.Count131072.C013597
import PlattCertificates.Count131072.C013598
import PlattCertificates.Count131072.C013599
import PlattCertificates.Count131072.C013600
import PlattCertificates.Count131072.C013601
import PlattCertificates.Count131072.C013602
import PlattCertificates.Count131072.C013603
import PlattCertificates.Count131072.C013604
import PlattCertificates.Count131072.C013605
import PlattCertificates.Count131072.C013606
import PlattCertificates.Count131072.C013607
import PlattCertificates.Count131072.C013608
import PlattCertificates.Count131072.C013609
import PlattCertificates.Count131072.C013610
import PlattCertificates.Count131072.C013611
import PlattCertificates.Count131072.C013612
import PlattCertificates.Count131072.C013613
import PlattCertificates.Count131072.C013614
import PlattCertificates.Count131072.C013615
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000112
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13584 : List PrefixCut := [⟨8,62465203,62465248⟩,
⟨63,470847780,470848116⟩,
⟨118,887577221,887577855⟩,
⟨128,964707016,964707704⟩]
theorem checked13584 : checkPrefixCuts (2^48) 1784414209 9 Manual.Count131072.C013584.packed 128 cuts13584 = true := by
 decide +kernel
def pointBounds13584 : List (Nat × Nat × Nat) := [(1784422400,94964504966418,94964882106470),(1784478720,94964913348995,94965290489338),(1784535040,94965330078436,94965707219077)]
theorem point_links_checked13584 : (cuts13584.take 3).map (fun c => (1784414209-1+2*2^9*c.k,94964442501215+c.lower,94964819641222+c.upper)) = pointBounds13584 := by
 decide +kernel
def cuts13585 : List PrefixCut := [⟨45,342741130,342741373⟩,
⟨100,763071991,763072537⟩,
⟨128,975203865,975204558⟩]
theorem checked13585 : checkPrefixCuts (2^48) 1784545281 9 Manual.Count131072.C013585.packed 128 cuts13585 = true := by
 decide +kernel
def pointBounds13585 : List (Nat × Nat × Nat) := [(1784591360,94965749949361,94966127090299),(1784647680,94966170280222,94966547421463)]
theorem point_links_checked13585 : (cuts13585.take 2).map (fun c => (1784545281-1+2*2^9*c.k,94965407208231+c.lower,94965784348926+c.upper)) = pointBounds13585 := by
 decide +kernel
def cuts13586 : List PrefixCut := [⟨27,204558155,204558297⟩,
⟨82,628647491,628647932⟩,
⟨128,985856334,985857025⟩]
theorem checked13586 : checkPrefixCuts (2^48) 1784676353 9 Manual.Count131072.C013586.packed 128 cuts13586 = true := by
 decide +kernel
def pointBounds13586 : List (Nat × Nat × Nat) := [(1784704000,94966586970251,94966964111781),(1784760320,94967011059587,94967388201416)]
theorem point_links_checked13586 : (cuts13586.take 2).map (fun c => (1784676353-1+2*2^9*c.k,94966382412096+c.lower,94966759553484+c.upper)) = pointBounds13586 := by
 decide +kernel
def cuts13587 : List PrefixCut := [⟨9,69863591,69863639⟩,
⟨64,480836897,480837234⟩,
⟨119,901259077,901259710⟩,
⟨128,967964000,967964681⟩]
theorem checked13587 : checkPrefixCuts (2^48) 1784807425 9 Manual.Count131072.C013587.packed 128 cuts13587 = true := by
 decide +kernel
def pointBounds13587 : List (Nat × Nat × Nat) := [(1784816640,94967438132021,94967815274148),(1784872960,94967849105327,94968226247743),(1784929280,94968269527507,94968646670219)]
theorem point_links_checked13587 : (cuts13587.take 3).map (fun c => (1784807425-1+2*2^9*c.k,94967368268430+c.lower,94967745410509+c.upper)) = pointBounds13587 := by
 decide +kernel
def cuts13588 : List PrefixCut := [⟨46,348500123,348500369⟩,
⟨101,764953633,764954173⟩,
⟨128,973885073,973885762⟩]
theorem checked13588 : checkPrefixCuts (2^48) 1784938497 9 Manual.Count131072.C013588.packed 128 cuts13588 = true := by
 decide +kernel
def pointBounds13588 : List (Nat × Nat × Nat) := [(1784985600,94968684732553,94969061875559),(1785041920,94969101186063,94969478329363)]
theorem point_links_checked13588 : (cuts13588.take 2).map (fun c => (1784938497-1+2*2^9*c.k,94968336232430+c.lower,94968713375190+c.upper)) = pointBounds13588 := by
 decide +kernel
def cuts13589 : List PrefixCut := [⟨28,213027862,213028011⟩,
⟨83,625828465,625828904⟩,
⟨128,962145589,962146262⟩]
theorem checked13589 : checkPrefixCuts (2^48) 1785069569 9 Manual.Count131072.C013589.packed 128 cuts13589 = true := by
 decide +kernel
def pointBounds13589 : List (Nat × Nat × Nat) := [(1785098240,94969523145365,94969900288963),(1785154560,94969935945968,94970313089856)]
theorem point_links_checked13589 : (cuts13589.take 2).map (fun c => (1785069569-1+2*2^9*c.k,94969310117503+c.lower,94969687260952+c.upper)) = pointBounds13589 := by
 decide +kernel
def cuts13590 : List PrefixCut := [⟨10,75051318,75051373⟩,
⟨65,500439260,500439612⟩,
⟨120,918246081,918246730⟩,
⟨128,977053285,977053976⟩]
theorem checked13590 : checkPrefixCuts (2^48) 1785200641 9 Manual.Count131072.C013590.packed 128 cuts13590 = true := by
 decide +kernel
def pointBounds13590 : List (Nat × Nat × Nat) := [(1785210880,94970347314410,94970724458587),(1785267200,94970772702352,94971149846826),(1785323520,94971190509173,94971567653944)]
theorem point_links_checked13590 : (cuts13590.take 3).map (fun c => (1785200641-1+2*2^9*c.k,94970272263092+c.lower,94970649407214+c.upper)) = pointBounds13590 := by
 decide +kernel
def cuts13591 : List PrefixCut := [⟨47,356936785,356937035⟩,
⟨102,769829945,769830488⟩,
⟨128,968468073,968468757⟩]
theorem checked13591 : checkPrefixCuts (2^48) 1785331713 9 Manual.Count131072.C013591.packed 128 cuts13591 = true := by
 decide +kernel
def pointBounds13591 : List (Nat × Nat × Nat) := [(1785379840,94971606253162,94971983398225),(1785436160,94972019146322,94972396291678)]
theorem point_links_checked13591 : (cuts13591.take 2).map (fun c => (1785331713-1+2*2^9*c.k,94971249316377+c.lower,94971626461190+c.upper)) = pointBounds13591 := by
 decide +kernel
def cuts13592 : List PrefixCut := [⟨29,222597347,222597503⟩,
⟨84,643819485,643819936⟩,
⟨128,981638917,981639604⟩]
theorem checked13592 : checkPrefixCuts (2^48) 1785462785 9 Manual.Count131072.C013592.packed 128 cuts13592 = true := by
 decide +kernel
def pointBounds13592 : List (Nat × Nat × Nat) := [(1785492480,94972440381797,94972817527450),(1785548800,94972861603935,94973238749883)]
theorem point_links_checked13592 : (cuts13592.take 2).map (fun c => (1785462785-1+2*2^9*c.k,94972217784450+c.lower,94972594929947+c.upper)) = pointBounds13592 := by
 decide +kernel
def cuts13593 : List PrefixCut := [⟨11,89537285,89537350⟩,
⟨66,507264936,507265291⟩,
⟨121,911738715,911739360⟩,
⟨128,964700818,964701502⟩]
theorem checked13593 : checkPrefixCuts (2^48) 1785593857 9 Manual.Count131072.C013593.packed 128 cuts13593 = true := by
 decide +kernel
def pointBounds13593 : List (Nat × Nat × Nat) := [(1785605120,94973288960652,94973666106901),(1785661440,94973706688303,94974083834842),(1785717760,94974111162082,94974488308911)]
theorem point_links_checked13593 : (cuts13593.take 3).map (fun c => (1785593857-1+2*2^9*c.k,94973199423367+c.lower,94973576569551+c.upper)) = pointBounds13593 := by
 decide +kernel
def cuts13594 : List PrefixCut := [⟨48,359222409,359222667⟩,
⟨103,779747663,779748213⟩,
⟨128,964471898,964472579⟩]
theorem checked13594 : checkPrefixCuts (2^48) 1785724929 9 Manual.Count131072.C013594.packed 128 cuts13594 = true := by
 decide +kernel
def pointBounds13594 : List (Nat × Nat × Nat) := [(1785774080,94974523346594,94974900493720),(1785830400,94974943871848,94975321019266)]
theorem point_links_checked13594 : (cuts13594.take 2).map (fun c => (1785724929-1+2*2^9*c.k,94974164124185+c.lower,94974541271053+c.upper)) = pointBounds13594 := by
 decide +kernel
def cuts13595 : List PrefixCut := [⟨30,230586463,230586624⟩,
⟨85,646987380,646987836⟩,
⟨128,969129538,969130222⟩]
theorem checked13595 : checkPrefixCuts (2^48) 1785856001 9 Manual.Count131072.C013595.packed 128 cuts13595 = true := by
 decide +kernel
def pointBounds13595 : List (Nat × Nat × Nat) := [(1785886720,94975359182546,94975736330256),(1785943040,94975775583463,94976152731468)]
theorem point_links_checked13595 : (cuts13595.take 2).map (fun c => (1785856001-1+2*2^9*c.k,94975128596083+c.lower,94975505743632+c.upper)) = pointBounds13595 := by
 decide +kernel
def cuts13596 : List PrefixCut := [⟨12,92039175,92039237⟩,
⟨67,502425120,502425470⟩,
⟨122,910749450,910750091⟩,
⟨128,956293120,956293793⟩]
theorem checked13596 : checkPrefixCuts (2^48) 1785987073 9 Manual.Count131072.C013596.packed 128 cuts13596 = true := by
 decide +kernel
def pointBounds13596 : List (Nat × Nat × Nat) := [(1785999360,94976189764796,94976566913091),(1786055680,94976600150741,94976977299324),(1786112000,94977008475071,94977385623945)]
theorem point_links_checked13596 : (cuts13596.take 3).map (fun c => (1785987073-1+2*2^9*c.k,94976097725621+c.lower,94976474873854+c.upper)) = pointBounds13596 := by
 decide +kernel
def cuts13597 : List PrefixCut := [⟨49,375374778,375375043⟩,
⟨104,794704156,794704716⟩,
⟨128,976708847,976709534⟩]
theorem checked13597 : checkPrefixCuts (2^48) 1786118145 9 Manual.Count131072.C013597.packed 128 cuts13597 = true := by
 decide +kernel
def pointBounds13597 : List (Nat × Nat × Nat) := [(1786168320,94977429393519,94977806542690),(1786224640,94977848722897,94978225872363)]
theorem point_links_checked13597 : (cuts13597.take 2).map (fun c => (1786118145-1+2*2^9*c.k,94977054018741+c.lower,94977431167647+c.upper)) = pointBounds13597 := by
 decide +kernel
def cuts13598 : List PrefixCut := [⟨31,239990250,239990420⟩,
⟨86,666856731,666857207⟩,
⟨128,977582898,977583592⟩]
theorem checked13598 : checkPrefixCuts (2^48) 1786249217 9 Manual.Count131072.C013598.packed 128 cuts13598 = true := by
 decide +kernel
def pointBounds13598 : List (Nat × Nat × Nat) := [(1786280960,94978270717838,94978647867601),(1786337280,94978697584319,94979074734388)]
theorem point_links_checked13598 : (cuts13598.take 2).map (fun c => (1786249217-1+2*2^9*c.k,94978030727588+c.lower,94978407877181+c.upper)) = pointBounds13598 := by
 decide +kernel
def cuts13599 : List PrefixCut := [⟨13,95012654,95012720⟩,
⟨68,505465537,505465889⟩,
⟨123,917638720,917639367⟩,
⟨128,957500347,957501021⟩]
theorem checked13599 : checkPrefixCuts (2^48) 1786380289 9 Manual.Count131072.C013599.packed 128 cuts13599 = true := by
 decide +kernel
def pointBounds13599 : List (Nat × Nat × Nat) := [(1786393600,94979103323140,94979480473493),(1786449920,94979513776023,94979890926662),(1786506240,94979925949206,94980303100140)]
theorem point_links_checked13599 : (cuts13599.take 3).map (fun c => (1786380289-1+2*2^9*c.k,94979008310486+c.lower,94979385460773+c.upper)) = pointBounds13599 := by
 decide +kernel
def cuts13600 : List PrefixCut := [⟨50,380176181,380176450⟩,
⟨105,793268620,793269184⟩,
⟨128,964520131,964520819⟩]
theorem checked13600 : checkPrefixCuts (2^48) 1786511361 9 Manual.Count131072.C013600.packed 128 cuts13600 = true := by
 decide +kernel
def pointBounds13600 : List (Nat × Nat × Nat) := [(1786562560,94980345987014,94980723138244),(1786618880,94980759079453,94981136230978)]
theorem point_links_checked13600 : (cuts13600.take 2).map (fun c => (1786511361-1+2*2^9*c.k,94979965810833+c.lower,94980342961794+c.upper)) = pointBounds13600 := by
 decide +kernel
def cuts13601 : List PrefixCut := [⟨32,241355309,241355477⟩,
⟨87,658517770,658518227⟩,
⟨128,973743984,973744668⟩]
theorem checked13601 : checkPrefixCuts (2^48) 1786642433 9 Manual.Count131072.C013601.packed 128 cuts13601 = true := by
 decide +kernel
def pointBounds13601 : List (Nat × Nat × Nat) := [(1786675200,94981171686273,94981548838090),(1786731520,94981588848734,94981966000840)]
theorem point_links_checked13601 : (cuts13601.take 2).map (fun c => (1786642433-1+2*2^9*c.k,94980930330964+c.lower,94981307482613+c.upper)) = pointBounds13601 := by
 decide +kernel
def cuts13602 : List PrefixCut := [⟨14,103025826,103025899⟩,
⟨69,512128087,512128451⟩,
⟨124,930196168,930196828⟩,
⟨128,961070308,961070988⟩]
theorem checked13602 : checkPrefixCuts (2^48) 1786773505 9 Manual.Count131072.C013602.packed 128 cuts13602 = true := by
 decide +kernel
def pointBounds13602 : List (Nat × Nat × Nat) := [(1786787840,94982007100774,94982384253180),(1786844160,94982416203035,94982793355732),(1786900480,94982834271116,94983211424109)]
theorem point_links_checked13602 : (cuts13602.take 3).map (fun c => (1786773505-1+2*2^9*c.k,94981904074948+c.lower,94982281227281+c.upper)) = pointBounds13602 := by
 decide +kernel
def cuts13603 : List PrefixCut := [⟨51,393638962,393639240⟩,
⟨106,808687943,808688519⟩,
⟨128,980059218,980059917⟩]
theorem checked13603 : checkPrefixCuts (2^48) 1786904577 9 Manual.Count131072.C013603.packed 128 cuts13603 = true := by
 decide +kernel
def pointBounds13603 : List (Nat × Nat × Nat) := [(1786956800,94983258784218,94983635937509),(1787013120,94983673833199,94984050986788)]
theorem point_links_checked13603 : (cuts13603.take 2).map (fun c => (1786904577-1+2*2^9*c.k,94982865145256+c.lower,94983242298269+c.upper)) = pointBounds13603 := by
 decide +kernel
def cuts13604 : List PrefixCut := [⟨33,244294739,244294910⟩,
⟨88,662625152,662625616⟩,
⟨128,963606925,963607597⟩]
theorem checked13604 : checkPrefixCuts (2^48) 1787035649 9 Manual.Count131072.C013604.packed 128 cuts13604 = true := by
 decide +kernel
def pointBounds13604 : List (Nat × Nat × Nat) := [(1787069440,94984089499213,94984466653096),(1787125760,94984507829626,94984884983802)]
theorem point_links_checked13604 : (cuts13604.take 2).map (fun c => (1787035649-1+2*2^9*c.k,94983845204474+c.lower,94984222358186+c.upper)) = pointBounds13604 := by
 decide +kernel
def cuts13605 : List PrefixCut := [⟨15,112925446,112925528⟩,
⟨70,539734220,539734602⟩,
⟨125,957710134,957710810⟩,
⟨128,981333096,981333789⟩]
theorem checked13605 : checkPrefixCuts (2^48) 1787166721 9 Manual.Count131072.C013605.packed 128 cuts13605 = true := by
 decide +kernel
def pointBounds13605 : List (Nat × Nat × Nat) := [(1787182080,94984921736845,94985298891311),(1787238400,94985348545619,94985725700385),(1787294720,94985766521533,94986143676593)]
theorem point_links_checked13605 : (cuts13605.take 3).map (fun c => (1787166721-1+2*2^9*c.k,94984808811399+c.lower,94985185965783+c.upper)) = pointBounds13605 := by
 decide +kernel
def cuts13606 : List PrefixCut := [⟨52,384260789,384261068⟩,
⟨107,809611924,809612506⟩,
⟨128,965827811,965828501⟩]
theorem checked13606 : checkPrefixCuts (2^48) 1787297793 9 Manual.Count131072.C013606.packed 128 cuts13606 = true := by
 decide +kernel
def pointBounds13606 : List (Nat × Nat × Nat) := [(1787351040,94986174405284,94986551560640),(1787407360,94986599756419,94986976912078)]
theorem point_links_checked13606 : (cuts13606.take 2).map (fun c => (1787297793-1+2*2^9*c.k,94985790144495+c.lower,94986167299572+c.upper)) = pointBounds13606 := by
 decide +kernel
def cuts13607 : List PrefixCut := [⟨34,257468686,257468866⟩,
⟨89,670982804,670983277⟩,
⟨128,967804265,967804947⟩]
theorem checked13607 : checkPrefixCuts (2^48) 1787428865 9 Manual.Count131072.C013607.packed 128 cuts13607 = true := by
 decide +kernel
def pointBounds13607 : List (Nat × Nat × Nat) := [(1787463680,94987013440992,94987390596939),(1787520000,94987426955110,94987804111350)]
theorem point_links_checked13607 : (cuts13607.take 2).map (fun c => (1787428865-1+2*2^9*c.k,94986755972306+c.lower,94987133128073+c.upper)) = pointBounds13607 := by
 decide +kernel
def cuts13608 : List PrefixCut := [⟨16,121246092,121246178⟩,
⟨71,535521412,535521791⟩,
⟨126,948523976,948524649⟩,
⟨128,962537179,962537863⟩]
theorem checked13608 : checkPrefixCuts (2^48) 1787559937 9 Manual.Count131072.C013608.packed 128 cuts13608 = true := by
 decide +kernel
def pointBounds13608 : List (Nat × Nat × Nat) := [(1787576320,94987845022663,94988222179198),(1787632640,94988259297983,94988636454811),(1787688960,94988672300547,94989049457669)]
theorem point_links_checked13608 : (cuts13608.take 3).map (fun c => (1787559937-1+2*2^9*c.k,94987723776571+c.lower,94988100933020+c.upper)) = pointBounds13608 := by
 decide +kernel
def cuts13609 : List PrefixCut := [⟨53,401810437,401810718⟩,
⟨108,816991251,816991823⟩,
⟨128,970496221,970496900⟩]
theorem checked13609 : checkPrefixCuts (2^48) 1787691009 9 Manual.Count131072.C013609.packed 128 cuts13609 = true := by
 decide +kernel
def pointBounds13609 : List (Nat × Nat × Nat) := [(1787745280,94989088124187,94989465281601),(1787801600,94989503305001,94989880462706)]
theorem point_links_checked13609 : (cuts13609.take 2).map (fun c => (1787691009-1+2*2^9*c.k,94988686313750+c.lower,94989063470883+c.upper)) = pointBounds13609 := by
 decide +kernel
def cuts13610 : List PrefixCut := [⟨35,263079747,263079935⟩,
⟨90,685004134,685004615⟩,
⟨128,975620456,975621143⟩]
theorem checked13610 : checkPrefixCuts (2^48) 1787822081 9 Manual.Count131072.C013610.packed 128 cuts13610 = true := by
 decide +kernel
def pointBounds13610 : List (Nat × Nat × Nat) := [(1787857920,94989919889718,94990297047718),(1787914240,94990341814105,94990718972398)]
theorem point_links_checked13610 : (cuts13610.take 2).map (fun c => (1787822081-1+2*2^9*c.k,94989656809971+c.lower,94990033967783+c.upper)) = pointBounds13610 := by
 decide +kernel
def cuts13611 : List PrefixCut := [⟨17,131137359,131137453⟩,
⟨72,545006476,545006854⟩,
⟨127,959492223,959492891⟩,
⟨128,964686986,964687658⟩]
theorem checked13611 : checkPrefixCuts (2^48) 1787953153 9 Manual.Count131072.C013611.packed 128 cuts13611 = true := by
 decide +kernel
def pointBounds13611 : List (Nat × Nat × Nat) := [(1787970560,94990763567786,94991140726379),(1788026880,94991177436903,94991554595780),(1788083200,94991591922650,94991969081817)]
theorem point_links_checked13611 : (cuts13611.take 3).map (fun c => (1787953153-1+2*2^9*c.k,94990632430427+c.lower,94991009588926+c.upper)) = pointBounds13611 := by
 decide +kernel
def cuts13612 : List PrefixCut := [⟨54,404870281,404870565⟩,
⟨109,823107787,823108368⟩,
⟨128,966347532,966348213⟩]
theorem checked13612 : checkPrefixCuts (2^48) 1788084225 9 Manual.Count131072.C013612.packed 128 cuts13612 = true := by
 decide +kernel
def pointBounds13612 : List (Nat × Nat × Nat) := [(1788139520,94992001987694,94992379147149),(1788195840,94992420225200,94992797384952)]
theorem point_links_checked13612 : (cuts13612.take 2).map (fun c => (1788084225-1+2*2^9*c.k,94991597117413+c.lower,94991974276584+c.upper)) = pointBounds13612 := by
 decide +kernel
def cuts13613 : List PrefixCut := [⟨36,269632800,269632991⟩,
⟨91,678400040,678400517⟩,
⟨128,960295606,960296284⟩]
theorem checked13613 : checkPrefixCuts (2^48) 1788215297 9 Manual.Count131072.C013613.packed 128 cuts13613 = true := by
 decide +kernel
def pointBounds13613 : List (Nat × Nat × Nat) := [(1788252160,94992833097745,94993210257788),(1788308480,94993241864985,94993619025314)]
theorem point_links_checked13613 : (cuts13613.take 2).map (fun c => (1788215297-1+2*2^9*c.k,94992563464945+c.lower,94992940624797+c.upper)) = pointBounds13613 := by
 decide +kernel
def cuts13614 : List PrefixCut := [⟨18,133469379,133469473⟩,
⟨73,557162901,557163290⟩,
⟨128,980685540,980686219⟩]
theorem checked13614 : checkPrefixCuts (2^48) 1788346369 9 Manual.Count131072.C013614.packed 128 cuts13614 = true := by
 decide +kernel
def pointBounds13614 : List (Nat × Nat × Nat) := [(1788364800,94993657229930,94994034390554),(1788421120,94994080923452,94994458084371),(1788477440,94994504446091,94994881607300)]
theorem point_links_checked13614 : (cuts13614.take 3).map (fun c => (1788346369-1+2*2^9*c.k,94993523760551+c.lower,94993900921081+c.upper)) = pointBounds13614 := by
 decide +kernel
def cuts13615 : List PrefixCut := [⟨55,406354983,406355269⟩,
⟨110,820880672,820881252⟩,
⟨128,959053010,959053688⟩]
theorem checked13615 : checkPrefixCuts (2^48) 1788477441 9 Manual.Count131072.C013615.packed 128 cuts13615 = true := by
 decide +kernel
def pointBounds13615 : List (Nat × Nat × Nat) := [(1788533760,94994910801074,94995287962569),(1788590080,94995325326763,94995702488552)]
theorem point_links_checked13615 : (cuts13615.take 2).map (fun c => (1788477441-1+2*2^9*c.k,94994504446091+c.lower,94994881607300+c.upper)) = pointBounds13615 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000112
