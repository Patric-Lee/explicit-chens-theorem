import PlattAssemblyKernel
import PlattCertificates.Count131072.C044544
import PlattCertificates.Count131072.C044545
import PlattCertificates.Count131072.C044546
import PlattCertificates.Count131072.C044547
import PlattCertificates.Count131072.C044548
import PlattCertificates.Count131072.C044549
import PlattCertificates.Count131072.C044550
import PlattCertificates.Count131072.C044551
import PlattCertificates.Count131072.C044552
import PlattCertificates.Count131072.C044553
import PlattCertificates.Count131072.C044554
import PlattCertificates.Count131072.C044555
import PlattCertificates.Count131072.C044556
import PlattCertificates.Count131072.C044557
import PlattCertificates.Count131072.C044558
import PlattCertificates.Count131072.C044559
import PlattCertificates.Count131072.C044560
import PlattCertificates.Count131072.C044561
import PlattCertificates.Count131072.C044562
import PlattCertificates.Count131072.C044563
import PlattCertificates.Count131072.C044564
import PlattCertificates.Count131072.C044565
import PlattCertificates.Count131072.C044566
import PlattCertificates.Count131072.C044567
import PlattCertificates.Count131072.C044568
import PlattCertificates.Count131072.C044569
import PlattCertificates.Count131072.C044570
import PlattCertificates.Count131072.C044571
import PlattCertificates.Count131072.C044572
import PlattCertificates.Count131072.C044573
import PlattCertificates.Count131072.C044574
import PlattCertificates.Count131072.C044575
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000142
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts44544 : List PrefixCut := [⟨64,281596839,281596996⟩]
theorem checked44544 : checkPrefixCuts (2^48) 5842403329 10 Manual.Count131072.C044544.packed 64 cuts44544 = true := by
 decide +kernel
def cuts44545 : List PrefixCut := [⟨23,102519918,102519979⟩,
⟨64,277784620,277784782⟩]
theorem checked44545 : checkPrefixCuts (2^48) 5842534401 10 Manual.Count131072.C044545.packed 64 cuts44545 = true := by
 decide +kernel
def pointBounds44545 : List (Nat × Nat × Nat) := [(5842581504,110215646035822,110216032331788)]
theorem point_links_checked44545 : (cuts44545.take 1).map (fun c => (5842534401-1+2*2^10*c.k,110215543515904+c.lower,110215929811809+c.upper)) = pointBounds44545 := by
 decide +kernel
def cuts44546 : List PrefixCut := [⟨49,213754061,213754180⟩,
⟨64,279801728,279801886⟩]
theorem checked44546 : checkPrefixCuts (2^48) 5842665473 10 Manual.Count131072.C044546.packed 64 cuts44546 = true := by
 decide +kernel
def pointBounds44546 : List (Nat × Nat × Nat) := [(5842765824,110216035054585,110216421350771)]
theorem point_links_checked44546 : (cuts44546.take 1).map (fun c => (5842665473-1+2*2^10*c.k,110215821300524+c.lower,110216207596591+c.upper)) = pointBounds44546 := by
 decide +kernel
def cuts44547 : List PrefixCut := [⟨64,279024672,279024826⟩]
theorem checked44547 : checkPrefixCuts (2^48) 5842796545 10 Manual.Count131072.C044547.packed 64 cuts44547 = true := by
 decide +kernel
def cuts44548 : List PrefixCut := [⟨11,47113699,47113723⟩,
⟨64,278488479,278488646⟩]
theorem checked44548 : checkPrefixCuts (2^48) 5842927617 10 Manual.Count131072.C044548.packed 64 cuts44548 = true := by
 decide +kernel
def pointBounds44548 : List (Nat × Nat × Nat) := [(5842950144,110216427240623,110216813537026)]
theorem point_links_checked44548 : (cuts44548.take 1).map (fun c => (5842927617-1+2*2^10*c.k,110216380126924+c.lower,110216766423303+c.upper)) = pointBounds44548 := by
 decide +kernel
def cuts44549 : List PrefixCut := [⟨37,164459938,164460032⟩,
⟨64,280505503,280505662⟩]
theorem checked44549 : checkPrefixCuts (2^48) 5843058689 10 Manual.Count131072.C044549.packed 64 cuts44549 = true := by
 decide +kernel
def pointBounds44549 : List (Nat × Nat × Nat) := [(5843134464,110216823075341,110217209371981)]
theorem point_links_checked44549 : (cuts44549.take 1).map (fun c => (5843058689-1+2*2^10*c.k,110216658615403+c.lower,110217044911949+c.upper)) = pointBounds44549 := by
 decide +kernel
def cuts44550 : List PrefixCut := [⟨63,277030915,277031074⟩,
⟨64,280980886,280981047⟩]
theorem checked44550 : checkPrefixCuts (2^48) 5843189761 10 Manual.Count131072.C044550.packed 64 cuts44550 = true := by
 decide +kernel
def pointBounds44550 : List (Nat × Nat × Nat) := [(5843318784,110217216151821,110217602448685)]
theorem point_links_checked44550 : (cuts44550.take 1).map (fun c => (5843189761-1+2*2^10*c.k,110216939120906+c.lower,110217325417611+c.upper)) = pointBounds44550 := by
 decide +kernel
def cuts44551 : List PrefixCut := [⟨64,277554520,277554679⟩]
theorem checked44551 : checkPrefixCuts (2^48) 5843320833 10 Manual.Count131072.C044551.packed 64 cuts44551 = true := by
 decide +kernel
def cuts44552 : List PrefixCut := [⟨25,107079853,107079914⟩,
⟨64,278078134,278078297⟩]
theorem checked44552 : checkPrefixCuts (2^48) 5843451905 10 Manual.Count131072.C044552.packed 64 cuts44552 = true := by
 decide +kernel
def pointBounds44552 : List (Nat × Nat × Nat) := [(5843503104,110217604736165,110217991033251)]
theorem point_links_checked44552 : (cuts44552.take 1).map (fun c => (5843451905-1+2*2^10*c.k,110217497656312+c.lower,110217883953337+c.upper)) = pointBounds44552 := by
 decide +kernel
def cuts44553 : List PrefixCut := [⟨51,224172848,224172972⟩,
⟨64,280769344,280769502⟩]
theorem checked44553 : checkPrefixCuts (2^48) 5843582977 10 Manual.Count131072.C044553.packed 64 cuts44553 = true := by
 decide +kernel
def pointBounds44553 : List (Nat × Nat × Nat) := [(5843687424,110217999907294,110218386204606)]
theorem point_links_checked44553 : (cuts44553.take 1).map (fun c => (5843582977-1+2*2^10*c.k,110217775734446+c.lower,110218162031634+c.upper)) = pointBounds44553 := by
 decide +kernel
def cuts44554 : List PrefixCut := [⟨64,278354706,278354874⟩]
theorem checked44554 : checkPrefixCuts (2^48) 5843714049 10 Manual.Count131072.C044554.packed 64 cuts44554 = true := by
 decide +kernel
def cuts44555 : List PrefixCut := [⟨13,56932135,56932167⟩,
⟨64,280082385,280082547⟩]
theorem checked44555 : checkPrefixCuts (2^48) 5843845121 10 Manual.Count131072.C044555.packed 64 cuts44555 = true := by
 decide +kernel
def pointBounds44555 : List (Nat × Nat × Nat) := [(5843871744,110218391790631,110218778088177)]
theorem point_links_checked44555 : (cuts44555.take 1).map (fun c => (5843845121-1+2*2^10*c.k,110218334858496+c.lower,110218721156010+c.upper)) = pointBounds44555 := by
 decide +kernel
def cuts44556 : List PrefixCut := [⟨39,172622035,172622132⟩,
⟨64,278775679,278775841⟩]
theorem checked44556 : checkPrefixCuts (2^48) 5843976193 10 Manual.Count131072.C044556.packed 64 cuts44556 = true := by
 decide +kernel
def pointBounds44556 : List (Nat × Nat × Nat) := [(5844056064,110218787562916,110219173860689)]
theorem point_links_checked44556 : (cuts44556.take 1).map (fun c => (5843976193-1+2*2^10*c.k,110218614940881+c.lower,110219001238557+c.upper)) = pointBounds44556 := by
 decide +kernel
def cuts44557 : List PrefixCut := [⟨64,280358825,280358981⟩]
theorem checked44557 : checkPrefixCuts (2^48) 5844107265 10 Manual.Count131072.C044557.packed 64 cuts44557 = true := by
 decide +kernel
def cuts44558 : List PrefixCut := [⟨1,4816279,4816282⟩,
⟨64,282568014,282568170⟩]
theorem checked44558 : checkPrefixCuts (2^48) 5844238337 10 Manual.Count131072.C044558.packed 64 cuts44558 = true := by
 decide +kernel
def pointBounds44558 : List (Nat × Nat × Nat) := [(5844240384,110219178891664,110219565189661)]
theorem point_links_checked44558 : (cuts44558.take 1).map (fun c => (5844238337-1+2*2^10*c.k,110219174075385+c.lower,110219560373379+c.upper)) = pointBounds44558 := by
 decide +kernel
def cuts44559 : List PrefixCut := [⟨27,115732066,115732139⟩,
⟨64,276878631,276878799⟩]
theorem checked44559 : checkPrefixCuts (2^48) 5844369409 10 Manual.Count131072.C044559.packed 64 cuts44559 = true := by
 decide +kernel
def pointBounds44559 : List (Nat × Nat × Nat) := [(5844424704,110219572375465,110219958673688)]
theorem point_links_checked44559 : (cuts44559.take 1).map (fun c => (5844369409-1+2*2^10*c.k,110219456643399+c.lower,110219842941549+c.upper)) = pointBounds44559 := by
 decide +kernel
def cuts44560 : List PrefixCut := [⟨53,236514710,236514845⟩,
⟨64,286552590,286552753⟩]
theorem checked44560 : checkPrefixCuts (2^48) 5844500481 10 Manual.Count131072.C044560.packed 64 cuts44560 = true := by
 decide +kernel
def pointBounds44560 : List (Nat × Nat × Nat) := [(5844609024,110219970036740,110220356335193)]
theorem point_links_checked44560 : (cuts44560.take 1).map (fun c => (5844500481-1+2*2^10*c.k,110219733522030+c.lower,110220119820348+c.upper)) = pointBounds44560 := by
 decide +kernel
def cuts44561 : List PrefixCut := [⟨64,279707616,279707782⟩]
theorem checked44561 : checkPrefixCuts (2^48) 5844631553 10 Manual.Count131072.C044561.packed 64 cuts44561 = true := by
 decide +kernel
def cuts44562 : List PrefixCut := [⟨15,66651162,66651200⟩,
⟨64,279990279,279990439⟩]
theorem checked44562 : checkPrefixCuts (2^48) 5844762625 10 Manual.Count131072.C044562.packed 64 cuts44562 = true := by
 decide +kernel
def pointBounds44562 : List (Nat × Nat × Nat) := [(5844793344,110220366433398,110220752732083)]
theorem point_links_checked44562 : (cuts44562.take 1).map (fun c => (5844762625-1+2*2^10*c.k,110220299782236+c.lower,110220686080883+c.upper)) = pointBounds44562 := by
 decide +kernel
def cuts44563 : List PrefixCut := [⟨41,175484305,175484409⟩,
⟨64,276083263,276083431⟩]
theorem checked44563 : checkPrefixCuts (2^48) 5844893697 10 Manual.Count131072.C044563.packed 64 cuts44563 = true := by
 decide +kernel
def pointBounds44563 : List (Nat × Nat × Nat) := [(5844977664,110220755256820,110221141555731)]
theorem point_links_checked44563 : (cuts44563.take 1).map (fun c => (5844893697-1+2*2^10*c.k,110220579772515+c.lower,110220966071322+c.upper)) = pointBounds44563 := by
 decide +kernel
def cuts44564 : List PrefixCut := [⟨64,282144726,282144893⟩]
theorem checked44564 : checkPrefixCuts (2^48) 5845024769 10 Manual.Count131072.C044564.packed 64 cuts44564 = true := by
 decide +kernel
def cuts44565 : List PrefixCut := [⟨3,13387151,13387158⟩,
⟨64,281897649,281897812⟩]
theorem checked44565 : checkPrefixCuts (2^48) 5845155841 10 Manual.Count131072.C044565.packed 64 cuts44565 = true := by
 decide +kernel
def pointBounds44565 : List (Nat × Nat × Nat) := [(5845161984,110221151387655,110221537686804)]
theorem point_links_checked44565 : (cuts44565.take 1).map (fun c => (5845155841-1+2*2^10*c.k,110221138000504+c.lower,110221524299646+c.upper)) = pointBounds44565 := by
 decide +kernel
def cuts44566 : List PrefixCut := [⟨29,127993112,127993189⟩,
⟨64,283913743,283913910⟩]
theorem checked44566 : checkPrefixCuts (2^48) 5845286913 10 Manual.Count131072.C044566.packed 64 cuts44566 = true := by
 decide +kernel
def pointBounds44566 : List (Nat × Nat × Nat) := [(5845346304,110221547891265,110221934190647)]
theorem point_links_checked44566 : (cuts44566.take 1).map (fun c => (5845286913-1+2*2^10*c.k,110221419898153+c.lower,110221806197458+c.upper)) = pointBounds44566 := by
 decide +kernel
def cuts44567 : List PrefixCut := [⟨55,242352140,242352282⟩,
⟨64,282751733,282751898⟩]
theorem checked44567 : checkPrefixCuts (2^48) 5845417985 10 Manual.Count131072.C044567.packed 64 cuts44567 = true := by
 decide +kernel
def pointBounds44567 : List (Nat × Nat × Nat) := [(5845530624,110221946164036,110222332463650)]
theorem point_links_checked44567 : (cuts44567.take 1).map (fun c => (5845417985-1+2*2^10*c.k,110221703811896+c.lower,110222090111368+c.upper)) = pointBounds44567 := by
 decide +kernel
def cuts44568 : List PrefixCut := [⟨64,282504638,282504798⟩]
theorem checked44568 : checkPrefixCuts (2^48) 5845549057 10 Manual.Count131072.C044568.packed 64 cuts44568 = true := by
 decide +kernel
def cuts44569 : List PrefixCut := [⟨17,73044733,73044777⟩,
⟨64,279657417,279657578⟩]
theorem checked44569 : checkPrefixCuts (2^48) 5845680129 10 Manual.Count131072.C044569.packed 64 cuts44569 = true := by
 decide +kernel
def pointBounds44569 : List (Nat × Nat × Nat) := [(5845714944,110222342113000,110222728412841)]
theorem point_links_checked44569 : (cuts44569.take 1).map (fun c => (5845680129-1+2*2^10*c.k,110222269068267+c.lower,110222655368064+c.upper)) = pointBounds44569 := by
 decide +kernel
def cuts44570 : List PrefixCut := [⟨43,184412527,184412633⟩,
⟨64,276617754,276617909⟩]
theorem checked44570 : checkPrefixCuts (2^48) 5845811201 10 Manual.Count131072.C044570.packed 64 cuts44570 = true := by
 decide +kernel
def pointBounds44570 : List (Nat × Nat × Nat) := [(5845899264,110222733138211,110223119438275)]
theorem point_links_checked44570 : (cuts44570.take 1).map (fun c => (5845811201-1+2*2^10*c.k,110222548725684+c.lower,110222935025642+c.upper)) = pointBounds44570 := by
 decide +kernel
def cuts44571 : List PrefixCut := [⟨64,280607841,280608005⟩]
theorem checked44571 : checkPrefixCuts (2^48) 5845942273 10 Manual.Count131072.C044571.packed 64 cuts44571 = true := by
 decide +kernel
def cuts44572 : List PrefixCut := [⟨5,21521995,21522009⟩,
⟨64,278916394,278916553⟩]
theorem checked44572 : checkPrefixCuts (2^48) 5846073345 10 Manual.Count131072.C044572.packed 64 cuts44572 = true := by
 decide +kernel
def pointBounds44572 : List (Nat × Nat × Nat) := [(5846083584,110223127473274,110223513773565)]
theorem point_links_checked44572 : (cuts44572.take 1).map (fun c => (5846073345-1+2*2^10*c.k,110223105951279+c.lower,110223492251556+c.upper)) = pointBounds44572 := by
 decide +kernel
def cuts44573 : List PrefixCut := [⟨31,136157867,136157942⟩,
⟨64,281798923,281799080⟩]
theorem checked44573 : checkPrefixCuts (2^48) 5846204417 10 Manual.Count131072.C044573.packed 64 cuts44573 = true := by
 decide +kernel
def pointBounds44573 : List (Nat × Nat × Nat) := [(5846267904,110223521025540,110223907326051)]
theorem point_links_checked44573 : (cuts44573.take 1).map (fun c => (5846204417-1+2*2^10*c.k,110223384867673+c.lower,110223771168109+c.upper)) = pointBounds44573 := by
 decide +kernel
def cuts44574 : List PrefixCut := [⟨57,252328160,252328310⟩,
⟨64,283766522,283766690⟩]
theorem checked44574 : checkPrefixCuts (2^48) 5846335489 10 Manual.Count131072.C044574.packed 64 cuts44574 = true := by
 decide +kernel
def pointBounds44574 : List (Nat × Nat × Nat) := [(5846452224,110223918994756,110224305295499)]
theorem point_links_checked44574 : (cuts44574.take 1).map (fun c => (5846335489-1+2*2^10*c.k,110223666666596+c.lower,110224052967189+c.upper)) = pointBounds44574 := by
 decide +kernel
def cuts44575 : List PrefixCut := [⟨64,279330934,279331096⟩]
theorem checked44575 : checkPrefixCuts (2^48) 5846466561 10 Manual.Count131072.C044575.packed 64 cuts44575 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000142
