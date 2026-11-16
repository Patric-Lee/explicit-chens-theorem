import PlattAssemblyKernel
import PlattCertificates.Count131072.C048608
import PlattCertificates.Count131072.C048609
import PlattCertificates.Count131072.C048610
import PlattCertificates.Count131072.C048611
import PlattCertificates.Count131072.C048612
import PlattCertificates.Count131072.C048613
import PlattCertificates.Count131072.C048614
import PlattCertificates.Count131072.C048615
import PlattCertificates.Count131072.C048616
import PlattCertificates.Count131072.C048617
import PlattCertificates.Count131072.C048618
import PlattCertificates.Count131072.C048619
import PlattCertificates.Count131072.C048620
import PlattCertificates.Count131072.C048621
import PlattCertificates.Count131072.C048622
import PlattCertificates.Count131072.C048623
import PlattCertificates.Count131072.C048624
import PlattCertificates.Count131072.C048625
import PlattCertificates.Count131072.C048626
import PlattCertificates.Count131072.C048627
import PlattCertificates.Count131072.C048628
import PlattCertificates.Count131072.C048629
import PlattCertificates.Count131072.C048630
import PlattCertificates.Count131072.C048631
import PlattCertificates.Count131072.C048632
import PlattCertificates.Count131072.C048633
import PlattCertificates.Count131072.C048634
import PlattCertificates.Count131072.C048635
import PlattCertificates.Count131072.C048636
import PlattCertificates.Count131072.C048637
import PlattCertificates.Count131072.C048638
import PlattCertificates.Count131072.C048639
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000269
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts48608 : List PrefixCut := [⟨64,256169424,256169572⟩]
theorem checked48608 : checkPrefixCuts (2^48) 6375079937 10 Manual.Count131072.C048608.packed 64 cuts48608 = true := by
 decide +kernel
def cuts48609 : List PrefixCut := [⟨14,55851476,55851505⟩,
⟨64,256340766,256340909⟩]
theorem checked48609 : checkPrefixCuts (2^48) 6375211009 10 Manual.Count131072.C048609.packed 64 cuts48609 = true := by
 decide +kernel
def pointBounds48609 : List (Nat × Nat × Nat) := [(6375239680,111305585982409,111305972904112)]
theorem point_links_checked48609 : (cuts48609.take 1).map (fun c => (6375211009-1+2*2^10*c.k,111305530130933+c.lower,111305917052607+c.upper)) = pointBounds48609 := by
 decide +kernel
def cuts48610 : List PrefixCut := [⟨48,190552337,190552445⟩,
⟨64,254834393,254834534⟩]
theorem checked48610 : checkPrefixCuts (2^48) 6375342081 10 Manual.Count131072.C048610.packed 64 cuts48610 = true := by
 decide +kernel
def pointBounds48610 : List (Nat × Nat × Nat) := [(6375440384,111305977024036,111306363945961)]
theorem point_links_checked48610 : (cuts48610.take 1).map (fun c => (6375342081-1+2*2^10*c.k,111305786471699+c.lower,111306173393516+c.upper)) = pointBounds48610 := by
 decide +kernel
def cuts48611 : List PrefixCut := [⟨64,258846714,258846858⟩]
theorem checked48611 : checkPrefixCuts (2^48) 6375473153 10 Manual.Count131072.C048611.packed 64 cuts48611 = true := by
 decide +kernel
def cuts48612 : List PrefixCut := [⟨18,72359576,72359618⟩,
⟨64,257693563,257693714⟩]
theorem checked48612 : checkPrefixCuts (2^48) 6375604225 10 Manual.Count131072.C048612.packed 64 cuts48612 = true := by
 decide +kernel
def pointBounds48612 : List (Nat × Nat × Nat) := [(6375641088,111306372512382,111306759434526)]
theorem point_links_checked48612 : (cuts48612.take 1).map (fun c => (6375604225-1+2*2^10*c.k,111306300152806+c.lower,111306687074908+c.upper)) = pointBounds48612 := by
 decide +kernel
def cuts48613 : List PrefixCut := [⟨52,208552633,208552752⟩,
⟨64,258350461,258350608⟩]
theorem checked48613 : checkPrefixCuts (2^48) 6375735297 10 Manual.Count131072.C048613.packed 64 cuts48613 = true := by
 decide +kernel
def pointBounds48613 : List (Nat × Nat × Nat) := [(6375841792,111306766399002,111307153321374)]
theorem point_links_checked48613 : (cuts48613.take 1).map (fun c => (6375735297-1+2*2^10*c.k,111306557846369+c.lower,111306944768622+c.upper)) = pointBounds48613 := by
 decide +kernel
def cuts48614 : List PrefixCut := [⟨64,255917063,255917212⟩]
theorem checked48614 : checkPrefixCuts (2^48) 6375866369 10 Manual.Count131072.C048614.packed 64 cuts48614 = true := by
 decide +kernel
def cuts48615 : List PrefixCut := [⟨22,87011490,87011543⟩,
⟨64,257015455,257015604⟩]
theorem checked48615 : checkPrefixCuts (2^48) 6375997441 10 Manual.Count131072.C048615.packed 64 cuts48615 = true := by
 decide +kernel
def pointBounds48615 : List (Nat × Nat × Nat) := [(6376042496,111307159125383,111307546047985)]
theorem point_links_checked48615 : (cuts48615.take 1).map (fun c => (6375997441-1+2*2^10*c.k,111307072113893+c.lower,111307459036442+c.upper)) = pointBounds48615 := by
 decide +kernel
def cuts48616 : List PrefixCut := [⟨56,221120883,221121003⟩,
⟨64,253787635,253787773⟩]
theorem checked48616 : checkPrefixCuts (2^48) 6376128513 10 Manual.Count131072.C048616.packed 64 cuts48616 = true := by
 decide +kernel
def pointBounds48616 : List (Nat × Nat × Nat) := [(6376243200,111307550250231,111307937173049)]
theorem point_links_checked48616 : (cuts48616.take 1).map (fun c => (6376128513-1+2*2^10*c.k,111307329129348+c.lower,111307716052046+c.upper)) = pointBounds48616 := by
 decide +kernel
def cuts48617 : List PrefixCut := [⟨64,257843640,257843786⟩]
theorem checked48617 : checkPrefixCuts (2^48) 6376259585 10 Manual.Count131072.C048617.packed 64 cuts48617 = true := by
 decide +kernel
def cuts48618 : List PrefixCut := [⟨26,101926438,101926499⟩,
⟨64,256911309,256911458⟩]
theorem checked48618 : checkPrefixCuts (2^48) 6376390657 10 Manual.Count131072.C048618.packed 64 cuts48618 = true := by
 decide +kernel
def pointBounds48618 : List (Nat × Nat × Nat) := [(6376443904,111307942687061,111308329610104)]
theorem point_links_checked48618 : (cuts48618.take 1).map (fun c => (6376390657-1+2*2^10*c.k,111307840760623+c.lower,111308227683605+c.upper)) = pointBounds48618 := by
 decide +kernel
def cuts48619 : List PrefixCut := [⟨60,236512627,236512763⟩,
⟨64,252977409,252977557⟩]
theorem checked48619 : checkPrefixCuts (2^48) 6376521729 10 Manual.Count131072.C048619.packed 64 cuts48619 = true := by
 decide +kernel
def pointBounds48619 : List (Nat × Nat × Nat) := [(6376644608,111308334184559,111308721107826)]
theorem point_links_checked48619 : (cuts48619.take 1).map (fun c => (6376521729-1+2*2^10*c.k,111308097671932+c.lower,111308484595063+c.upper)) = pointBounds48619 := by
 decide +kernel
def cuts48620 : List PrefixCut := [⟨64,257695326,257695471⟩]
theorem checked48620 : checkPrefixCuts (2^48) 6376652801 10 Manual.Count131072.C048620.packed 64 cuts48620 = true := by
 decide +kernel
def cuts48621 : List PrefixCut := [⟨30,118649286,118649357⟩,
⟨64,252040078,252040225⟩]
theorem checked48621 : checkPrefixCuts (2^48) 6376783873 10 Manual.Count131072.C048621.packed 64 cuts48621 = true := by
 decide +kernel
def pointBounds48621 : List (Nat × Nat × Nat) := [(6376845312,111308726993953,111309113917448)]
theorem point_links_checked48621 : (cuts48621.take 1).map (fun c => (6376783873-1+2*2^10*c.k,111308608344667+c.lower,111308995268091+c.upper)) = pointBounds48621 := by
 decide +kernel
def cuts48622 : List PrefixCut := [⟨64,256448832,256448975⟩]
theorem checked48622 : checkPrefixCuts (2^48) 6376914945 10 Manual.Count131072.C048622.packed 64 cuts48622 = true := by
 decide +kernel
def pointBounds48622 : List (Nat × Nat × Nat) := [(6377046016,111309116833577,111309503757291)]
theorem point_links_checked48622 : (cuts48622.take 1).map (fun c => (6376914945-1+2*2^10*c.k,111308860384745+c.lower,111309247308316+c.upper)) = pointBounds48622 := by
 decide +kernel
def cuts48623 : List PrefixCut := [⟨64,254324925,254325069⟩]
theorem checked48623 : checkPrefixCuts (2^48) 6377046017 10 Manual.Count131072.C048623.packed 64 cuts48623 = true := by
 decide +kernel
def cuts48624 : List PrefixCut := [⟨34,139474856,139474933⟩,
⟨64,261646510,261646654⟩]
theorem checked48624 : checkPrefixCuts (2^48) 6377177089 10 Manual.Count131072.C048624.packed 64 cuts48624 = true := by
 decide +kernel
def pointBounds48624 : List (Nat × Nat × Nat) := [(6377246720,111309510633358,111309897557293)]
theorem point_links_checked48624 : (cuts48624.take 1).map (fun c => (6377177089-1+2*2^10*c.k,111309371158502+c.lower,111309758082360+c.upper)) = pointBounds48624 := by
 decide +kernel
def cuts48625 : List PrefixCut := [⟨64,252328297,252328441⟩]
theorem checked48625 : checkPrefixCuts (2^48) 6377308161 10 Manual.Count131072.C048625.packed 64 cuts48625 = true := by
 decide +kernel
def cuts48626 : List PrefixCut := [⟨4,16506867,16506876⟩,
⟨64,257354584,257354722⟩]
theorem checked48626 : checkPrefixCuts (2^48) 6377439233 10 Manual.Count131072.C048626.packed 64 cuts48626 = true := by
 decide +kernel
def pointBounds48626 : List (Nat × Nat × Nat) := [(6377447424,111309901640176,111310288564331)]
theorem point_links_checked48626 : (cuts48626.take 1).map (fun c => (6377439233-1+2*2^10*c.k,111309885133309+c.lower,111310272057455+c.upper)) = pointBounds48626 := by
 decide +kernel
def cuts48627 : List PrefixCut := [⟨38,154383736,154383820⟩,
⟨64,257261044,257261188⟩]
theorem checked48627 : checkPrefixCuts (2^48) 6377570305 10 Manual.Count131072.C048627.packed 64 cuts48627 = true := by
 decide +kernel
def pointBounds48627 : List (Nat × Nat × Nat) := [(6377648128,111310296871629,111310683795997)]
theorem point_links_checked48627 : (cuts48627.take 1).map (fun c => (6377570305-1+2*2^10*c.k,111310142487893+c.lower,111310529412177+c.upper)) = pointBounds48627 := by
 decide +kernel
def cuts48628 : List PrefixCut := [⟨64,257741241,257741396⟩]
theorem checked48628 : checkPrefixCuts (2^48) 6377701377 10 Manual.Count131072.C048628.packed 64 cuts48628 = true := by
 decide +kernel
def cuts48629 : List PrefixCut := [⟨8,32791012,32791030⟩,
⟨64,253940518,253940664⟩]
theorem checked48629 : checkPrefixCuts (2^48) 6377832449 10 Manual.Count131072.C048629.packed 64 cuts48629 = true := by
 decide +kernel
def pointBounds48629 : List (Nat × Nat × Nat) := [(6377848832,111310690281190,111311077205791)]
theorem point_links_checked48629 : (cuts48629.take 1).map (fun c => (6377832449-1+2*2^10*c.k,111310657490178+c.lower,111311044414761+c.upper)) = pointBounds48629 := by
 decide +kernel
def cuts48630 : List PrefixCut := [⟨42,169952757,169952851⟩,
⟨64,257465832,257465979⟩]
theorem checked48630 : checkPrefixCuts (2^48) 6377963521 10 Manual.Count131072.C048630.packed 64 cuts48630 = true := by
 decide +kernel
def pointBounds48630 : List (Nat × Nat × Nat) := [(6378049536,111311081383453,111311468308276)]
theorem point_links_checked48630 : (cuts48630.take 1).map (fun c => (6377963521-1+2*2^10*c.k,111310911430696+c.lower,111311298355425+c.upper)) = pointBounds48630 := by
 decide +kernel
def cuts48631 : List PrefixCut := [⟨64,255960077,255960225⟩]
theorem checked48631 : checkPrefixCuts (2^48) 6378094593 10 Manual.Count131072.C048631.packed 64 cuts48631 = true := by
 decide +kernel
def cuts48632 : List PrefixCut := [⟨12,46734211,46734238⟩,
⟨64,256616753,256616902⟩]
theorem checked48632 : checkPrefixCuts (2^48) 6378225665 10 Manual.Count131072.C048632.packed 64 cuts48632 = true := by
 decide +kernel
def pointBounds48632 : List (Nat × Nat × Nat) := [(6378250240,111311471590816,111311858515867)]
theorem point_links_checked48632 : (cuts48632.take 1).map (fun c => (6378225665-1+2*2^10*c.k,111311424856605+c.lower,111311811781629+c.upper)) = pointBounds48632 := by
 decide +kernel
def cuts48633 : List PrefixCut := [⟨46,186137661,186137767⟩,
⟨64,256920430,256920578⟩]
theorem checked48633 : checkPrefixCuts (2^48) 6378356737 10 Manual.Count131072.C048633.packed 64 cuts48633 = true := by
 decide +kernel
def pointBounds48633 : List (Nat × Nat × Nat) := [(6378450944,111311867611019,111312254536298)]
theorem point_links_checked48633 : (cuts48633.take 1).map (fun c => (6378356737-1+2*2^10*c.k,111311681473358+c.lower,111312068398531+c.upper)) = pointBounds48633 := by
 decide +kernel
def cuts48634 : List PrefixCut := [⟨64,253429003,253429145⟩]
theorem checked48634 : checkPrefixCuts (2^48) 6378487809 10 Manual.Count131072.C048634.packed 64 cuts48634 = true := by
 decide +kernel
def cuts48635 : List PrefixCut := [⟨16,65838618,65838659⟩,
⟨64,261322601,261322752⟩]
theorem checked48635 : checkPrefixCuts (2^48) 6378618881 10 Manual.Count131072.C048635.packed 64 cuts48635 = true := by
 decide +kernel
def pointBounds48635 : List (Nat × Nat × Nat) := [(6378651648,111312257661409,111312644586913)]
theorem point_links_checked48635 : (cuts48635.take 1).map (fun c => (6378618881-1+2*2^10*c.k,111312191822791+c.lower,111312578748254+c.upper)) = pointBounds48635 := by
 decide +kernel
def cuts48636 : List PrefixCut := [⟨50,201349741,201349857⟩,
⟨64,257213460,257213608⟩]
theorem checked48636 : checkPrefixCuts (2^48) 6378749953 10 Manual.Count131072.C048636.packed 64 cuts48636 = true := by
 decide +kernel
def pointBounds48636 : List (Nat × Nat × Nat) := [(6378852352,111312654495133,111313041420863)]
theorem point_links_checked48636 : (cuts48636.take 1).map (fun c => (6378749953-1+2*2^10*c.k,111312453145392+c.lower,111312840071006+c.upper)) = pointBounds48636 := by
 decide +kernel
def cuts48637 : List PrefixCut := [⟨64,253457492,253457636⟩]
theorem checked48637 : checkPrefixCuts (2^48) 6378881025 10 Manual.Count131072.C048637.packed 64 cuts48637 = true := by
 decide +kernel
def cuts48638 : List PrefixCut := [⟨20,80881149,80881194⟩,
⟨64,253893554,253893695⟩]
theorem checked48638 : checkPrefixCuts (2^48) 6379012097 10 Manual.Count131072.C048638.packed 64 cuts48638 = true := by
 decide +kernel
def pointBounds48638 : List (Nat × Nat × Nat) := [(6379053056,111313044697493,111313431623444)]
theorem point_links_checked48638 : (cuts48638.take 1).map (fun c => (6379012097-1+2*2^10*c.k,111312963816344+c.lower,111313350742250+c.upper)) = pointBounds48638 := by
 decide +kernel
def cuts48639 : List PrefixCut := [⟨54,217486520,217486636⟩,
⟨64,257021099,257021238⟩]
theorem checked48639 : checkPrefixCuts (2^48) 6379143169 10 Manual.Count131072.C048639.packed 64 cuts48639 = true := by
 decide +kernel
def pointBounds48639 : List (Nat × Nat × Nat) := [(6379253760,111313435196418,111313822122581)]
theorem point_links_checked48639 : (cuts48639.take 1).map (fun c => (6379143169-1+2*2^10*c.k,111313217709898+c.lower,111313604635945+c.upper)) = pointBounds48639 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000269
