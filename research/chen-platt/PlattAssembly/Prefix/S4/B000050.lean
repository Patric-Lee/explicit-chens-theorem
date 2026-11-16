import PlattAssemblyKernel
import PlattCertificates.Count131072.C031600
import PlattCertificates.Count131072.C031601
import PlattCertificates.Count131072.C031602
import PlattCertificates.Count131072.C031603
import PlattCertificates.Count131072.C031604
import PlattCertificates.Count131072.C031605
import PlattCertificates.Count131072.C031606
import PlattCertificates.Count131072.C031607
import PlattCertificates.Count131072.C031608
import PlattCertificates.Count131072.C031609
import PlattCertificates.Count131072.C031610
import PlattCertificates.Count131072.C031611
import PlattCertificates.Count131072.C031612
import PlattCertificates.Count131072.C031613
import PlattCertificates.Count131072.C031614
import PlattCertificates.Count131072.C031615
import PlattCertificates.Count131072.C031616
import PlattCertificates.Count131072.C031617
import PlattCertificates.Count131072.C031618
import PlattCertificates.Count131072.C031619
import PlattCertificates.Count131072.C031620
import PlattCertificates.Count131072.C031621
import PlattCertificates.Count131072.C031622
import PlattCertificates.Count131072.C031623
import PlattCertificates.Count131072.C031624
import PlattCertificates.Count131072.C031625
import PlattCertificates.Count131072.C031626
import PlattCertificates.Count131072.C031627
import PlattCertificates.Count131072.C031628
import PlattCertificates.Count131072.C031629
import PlattCertificates.Count131072.C031630
import PlattCertificates.Count131072.C031631
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000050
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts31600 : List PrefixCut := [⟨96,298050535,298050704⟩,
⟨128,396833376,396833601⟩]
theorem checked31600 : checkPrefixCuts (2^48) 4145807361 9 Manual.Count131072.C031600.packed 128 cuts31600 = true := by
 decide +kernel
def pointBounds31600 : List (Nat × Nat × Nat) := [(4145905664,105888804245863,105889187939282)]
theorem point_links_checked31600 : (cuts31600.take 1).map (fun c => (4145807361-1+2*2^9*c.k,105888506195328+c.lower,105888889888578+c.upper)) = pointBounds31600 := by
 decide +kernel
def cuts31601 : List PrefixCut := [⟨95,298991632,298991794⟩,
⟨128,398518155,398518378⟩]
theorem checked31601 : checkPrefixCuts (2^48) 4145938433 9 Manual.Count131072.C031601.packed 128 cuts31601 = true := by
 decide +kernel
def pointBounds31601 : List (Nat × Nat × Nat) := [(4146035712,105889202020336,105889585713973)]
theorem point_links_checked31601 : (cuts31601.take 1).map (fun c => (4145938433-1+2*2^9*c.k,105888903028704+c.lower,105889286722179+c.upper)) = pointBounds31601 := by
 decide +kernel
def cuts31602 : List PrefixCut := [⟨94,297217126,297217299⟩,
⟨128,402986186,402986417⟩]
theorem checked31602 : checkPrefixCuts (2^48) 4146069505 9 Manual.Count131072.C031602.packed 128 cuts31602 = true := by
 decide +kernel
def pointBounds31602 : List (Nat × Nat × Nat) := [(4146165760,105889598763985,105889982457856)]
theorem point_links_checked31602 : (cuts31602.take 1).map (fun c => (4146069505-1+2*2^9*c.k,105889301546859+c.lower,105889685240557+c.upper)) = pointBounds31602 := by
 decide +kernel
def cuts31603 : List PrefixCut := [⟨93,291505282,291505447⟩,
⟨128,405417272,405417503⟩]
theorem checked31603 : checkPrefixCuts (2^48) 4146200577 9 Manual.Count131072.C031603.packed 128 cuts31603 = true := by
 decide +kernel
def pointBounds31603 : List (Nat × Nat × Nat) := [(4146295808,105889996038327,105890379732421)]
theorem point_links_checked31603 : (cuts31603.take 1).map (fun c => (4146200577-1+2*2^9*c.k,105889704533045+c.lower,105890088226974+c.upper)) = pointBounds31603 := by
 decide +kernel
def cuts31604 : List PrefixCut := [⟨92,289052245,289052415⟩,
⟨128,401195691,401195921⟩]
theorem checked31604 : checkPrefixCuts (2^48) 4146331649 9 Manual.Count131072.C031604.packed 128 cuts31604 = true := by
 decide +kernel
def pointBounds31604 : List (Nat × Nat × Nat) := [(4146425856,105890399002562,105890782696892)]
theorem point_links_checked31604 : (cuts31604.take 1).map (fun c => (4146331649-1+2*2^9*c.k,105890109950317+c.lower,105890493644477+c.upper)) = pointBounds31604 := by
 decide +kernel
def cuts31605 : List PrefixCut := [⟨91,285988442,285988605⟩,
⟨128,399485973,399486202⟩]
theorem checked31605 : checkPrefixCuts (2^48) 4146462721 9 Manual.Count131072.C031605.packed 128 cuts31605 = true := by
 decide +kernel
def pointBounds31605 : List (Nat × Nat × Nat) := [(4146555904,105890797134450,105891180829003)]
theorem point_links_checked31605 : (cuts31605.take 1).map (fun c => (4146462721-1+2*2^9*c.k,105890511146008+c.lower,105890894840398+c.upper)) = pointBounds31605 := by
 decide +kernel
def cuts31606 : List PrefixCut := [⟨90,280209658,280209801⟩,
⟨128,399609106,399609315⟩]
theorem checked31606 : checkPrefixCuts (2^48) 4146593793 9 Manual.Count131072.C031606.packed 128 cuts31606 = true := by
 decide +kernel
def pointBounds31606 : List (Nat × Nat × Nat) := [(4146685952,105891190841639,105891574536401)]
theorem point_links_checked31606 : (cuts31606.take 1).map (fun c => (4146593793-1+2*2^9*c.k,105890910631981+c.lower,105891294326600+c.upper)) = pointBounds31606 := by
 decide +kernel
def cuts31607 : List PrefixCut := [⟨89,284001962,284002120⟩,
⟨128,407063012,407063244⟩]
theorem checked31607 : checkPrefixCuts (2^48) 4146724865 9 Manual.Count131072.C031607.packed 128 cuts31607 = true := by
 decide +kernel
def pointBounds31607 : List (Nat × Nat × Nat) := [(4146816000,105891594243049,105891977938035)]
theorem point_links_checked31607 : (cuts31607.take 1).map (fun c => (4146724865-1+2*2^9*c.k,105891310241087+c.lower,105891693935915+c.upper)) = pointBounds31607 := by
 decide +kernel
def cuts31608 : List PrefixCut := [⟨88,276594552,276594702⟩,
⟨128,397886982,397887202⟩]
theorem checked31608 : checkPrefixCuts (2^48) 4146855937 9 Manual.Count131072.C031608.packed 128 cuts31608 = true := by
 decide +kernel
def pointBounds31608 : List (Nat × Nat × Nat) := [(4146946048,105891993898651,105892377593861)]
theorem point_links_checked31608 : (cuts31608.take 1).map (fun c => (4146855937-1+2*2^9*c.k,105891717304099+c.lower,105892100999159+c.upper)) = pointBounds31608 := by
 decide +kernel
def cuts31609 : List PrefixCut := [⟨87,274481751,274481906⟩,
⟨128,407172993,407173218⟩]
theorem checked31609 : checkPrefixCuts (2^48) 4146987009 9 Manual.Count131072.C031609.packed 128 cuts31609 = true := by
 decide +kernel
def pointBounds31609 : List (Nat × Nat × Nat) := [(4147076096,105892389672832,105892773368267)]
theorem point_links_checked31609 : (cuts31609.take 1).map (fun c => (4146987009-1+2*2^9*c.k,105892115191081+c.lower,105892498886361+c.upper)) = pointBounds31609 := by
 decide +kernel
def cuts31610 : List PrefixCut := [⟨86,263749375,263749527⟩,
⟨128,394264578,394264806⟩]
theorem checked31610 : checkPrefixCuts (2^48) 4147118081 9 Manual.Count131072.C031610.packed 128 cuts31610 = true := by
 decide +kernel
def pointBounds31610 : List (Nat × Nat × Nat) := [(4147206144,105892786113449,105893169809106)]
theorem point_links_checked31610 : (cuts31610.take 1).map (fun c => (4147118081-1+2*2^9*c.k,105892522364074+c.lower,105892906059579+c.upper)) = pointBounds31610 := by
 decide +kernel
def cuts31611 : List PrefixCut := [⟨85,266184391,266184546⟩,
⟨128,402735784,402736013⟩]
theorem checked31611 : checkPrefixCuts (2^48) 4147249153 9 Manual.Count131072.C031611.packed 128 cuts31611 = true := by
 decide +kernel
def pointBounds31611 : List (Nat × Nat × Nat) := [(4147336192,105893182813043,105893566508931)]
theorem point_links_checked31611 : (cuts31611.take 1).map (fun c => (4147249153-1+2*2^9*c.k,105892916628652+c.lower,105893300324385+c.upper)) = pointBounds31611 := by
 decide +kernel
def cuts31612 : List PrefixCut := [⟨84,264615056,264615205⟩,
⟨128,401840792,401841023⟩]
theorem checked31612 : checkPrefixCuts (2^48) 4147380225 9 Manual.Count131072.C031612.packed 128 cuts31612 = true := by
 decide +kernel
def pointBounds31612 : List (Nat × Nat × Nat) := [(4147466240,105893583979492,105893967675603)]
theorem point_links_checked31612 : (cuts31612.take 1).map (fun c => (4147380225-1+2*2^9*c.k,105893319364436+c.lower,105893703060398+c.upper)) = pointBounds31612 := by
 decide +kernel
def cuts31613 : List PrefixCut := [⟨83,260331210,260331357⟩,
⟨128,402642445,402642671⟩]
theorem checked31613 : checkPrefixCuts (2^48) 4147511297 9 Manual.Count131072.C031613.packed 128 cuts31613 = true := by
 decide +kernel
def pointBounds31613 : List (Nat × Nat × Nat) := [(4147596288,105893981536438,105894365232778)]
theorem point_links_checked31613 : (cuts31613.take 1).map (fun c => (4147511297-1+2*2^9*c.k,105893721205228+c.lower,105894104901421+c.upper)) = pointBounds31613 := by
 decide +kernel
def cuts31614 : List PrefixCut := [⟨82,254147457,254147601⟩,
⟨128,402493946,402494170⟩]
theorem checked31614 : checkPrefixCuts (2^48) 4147642369 9 Manual.Count131072.C031614.packed 128 cuts31614 = true := by
 decide +kernel
def pointBounds31614 : List (Nat × Nat × Nat) := [(4147726336,105894377995130,105894761691693)]
theorem point_links_checked31614 : (cuts31614.take 1).map (fun c => (4147642369-1+2*2^9*c.k,105894123847673+c.lower,105894507544092+c.upper)) = pointBounds31614 := by
 decide +kernel
def cuts31615 : List PrefixCut := [⟨81,254682356,254682494⟩,
⟨128,401124100,401124316⟩]
theorem checked31615 : checkPrefixCuts (2^48) 4147773441 9 Manual.Count131072.C031615.packed 128 cuts31615 = true := by
 decide +kernel
def pointBounds31615 : List (Nat × Nat × Nat) := [(4147856384,105894781023975,105895164720756)]
theorem point_links_checked31615 : (cuts31615.take 1).map (fun c => (4147773441-1+2*2^9*c.k,105894526341619+c.lower,105894910038262+c.upper)) = pointBounds31615 := by
 decide +kernel
def cuts31616 : List PrefixCut := [⟨80,250602793,250602940⟩,
⟨128,401586376,401586609⟩]
theorem checked31616 : checkPrefixCuts (2^48) 4147904513 9 Manual.Count131072.C031616.packed 128 cuts31616 = true := by
 decide +kernel
def pointBounds31616 : List (Nat × Nat × Nat) := [(4147986432,105895178068512,105895561765518)]
theorem point_links_checked31616 : (cuts31616.take 1).map (fun c => (4147904513-1+2*2^9*c.k,105894927465719+c.lower,105895311162578+c.upper)) = pointBounds31616 := by
 decide +kernel
def cuts31617 : List PrefixCut := [⟨79,247948514,247948653⟩,
⟨128,404355820,404356043⟩]
theorem checked31617 : checkPrefixCuts (2^48) 4148035585 9 Manual.Count131072.C031617.packed 128 cuts31617 = true := by
 decide +kernel
def pointBounds31617 : List (Nat × Nat × Nat) := [(4148116480,105895577000609,105895960697840)]
theorem point_links_checked31617 : (cuts31617.take 1).map (fun c => (4148035585-1+2*2^9*c.k,105895329052095+c.lower,105895712749187+c.upper)) = pointBounds31617 := by
 decide +kernel
def cuts31618 : List PrefixCut := [⟨78,246176510,246176647⟩,
⟨128,401425389,401425610⟩]
theorem checked31618 : checkPrefixCuts (2^48) 4148166657 9 Manual.Count131072.C031618.packed 128 cuts31618 = true := by
 decide +kernel
def pointBounds31618 : List (Nat × Nat × Nat) := [(4148246528,105895979584425,105896363281877)]
theorem point_links_checked31618 : (cuts31618.take 1).map (fun c => (4148166657-1+2*2^9*c.k,105895733407915+c.lower,105896117105230+c.upper)) = pointBounds31618 := by
 decide +kernel
def cuts31619 : List PrefixCut := [⟨77,241079797,241079935⟩,
⟨128,403176784,403177014⟩]
theorem checked31619 : checkPrefixCuts (2^48) 4148297729 9 Manual.Count131072.C031619.packed 128 cuts31619 = true := by
 decide +kernel
def pointBounds31619 : List (Nat × Nat × Nat) := [(4148376576,105896375913101,105896759610775)]
theorem point_links_checked31619 : (cuts31619.take 1).map (fun c => (4148297729-1+2*2^9*c.k,105896134833304+c.lower,105896518530840+c.upper)) = pointBounds31619 := by
 decide +kernel
def cuts31620 : List PrefixCut := [⟨76,241547202,241547330⟩,
⟨128,402757031,402757250⟩]
theorem checked31620 : checkPrefixCuts (2^48) 4148428801 9 Manual.Count131072.C031620.packed 128 cuts31620 = true := by
 decide +kernel
def pointBounds31620 : List (Nat × Nat × Nat) := [(4148506624,105896779557290,105897163255184)]
theorem point_links_checked31620 : (cuts31620.take 1).map (fun c => (4148428801-1+2*2^9*c.k,105896538010088+c.lower,105896921707854+c.upper)) = pointBounds31620 := by
 decide +kernel
def cuts31621 : List PrefixCut := [⟨75,233940561,233940695⟩,
⟨128,401115854,401116082⟩]
theorem checked31621 : checkPrefixCuts (2^48) 4148559873 9 Manual.Count131072.C031621.packed 128 cuts31621 = true := by
 decide +kernel
def pointBounds31621 : List (Nat × Nat × Nat) := [(4148636672,105897174707680,105897558405799)]
theorem point_links_checked31621 : (cuts31621.take 1).map (fun c => (4148559873-1+2*2^9*c.k,105896940767119+c.lower,105897324465104+c.upper)) = pointBounds31621 := by
 decide +kernel
def cuts31622 : List PrefixCut := [⟨74,229319703,229319832⟩,
⟨128,396625440,396625664⟩]
theorem checked31622 : checkPrefixCuts (2^48) 4148690945 9 Manual.Count131072.C031622.packed 128 cuts31622 = true := by
 decide +kernel
def pointBounds31622 : List (Nat × Nat × Nat) := [(4148766720,105897571202676,105897954901018)]
theorem point_links_checked31622 : (cuts31622.take 1).map (fun c => (4148690945-1+2*2^9*c.k,105897341882973+c.lower,105897725581186+c.upper)) = pointBounds31622 := by
 decide +kernel
def cuts31623 : List PrefixCut := [⟨73,227752033,227752169⟩,
⟨128,395798779,395799015⟩]
theorem checked31623 : checkPrefixCuts (2^48) 4148822017 9 Manual.Count131072.C031623.packed 128 cuts31623 = true := by
 decide +kernel
def pointBounds31623 : List (Nat × Nat × Nat) := [(4148896768,105897966260446,105898349959019)]
theorem point_links_checked31623 : (cuts31623.take 1).map (fun c => (4148822017-1+2*2^9*c.k,105897738508413+c.lower,105898122206850+c.upper)) = pointBounds31623 := by
 decide +kernel
def cuts31624 : List PrefixCut := [⟨72,226862918,226863043⟩,
⟨128,403587994,403588216⟩]
theorem checked31624 : checkPrefixCuts (2^48) 4148953089 9 Manual.Count131072.C031624.packed 128 cuts31624 = true := by
 decide +kernel
def pointBounds31624 : List (Nat × Nat × Nat) := [(4149026816,105898361170110,105898744868908)]
theorem point_links_checked31624 : (cuts31624.take 1).map (fun c => (4148953089-1+2*2^9*c.k,105898134307192+c.lower,105898518005865+c.upper)) = pointBounds31624 := by
 decide +kernel
def cuts31625 : List PrefixCut := [⟨71,220003983,220004110⟩,
⟨128,397334035,397334265⟩]
theorem checked31625 : checkPrefixCuts (2^48) 4149084161 9 Manual.Count131072.C031625.packed 128 cuts31625 = true := by
 decide +kernel
def pointBounds31625 : List (Nat × Nat × Nat) := [(4149156864,105898757899169,105899141598191)]
theorem point_links_checked31625 : (cuts31625.take 1).map (fun c => (4149084161-1+2*2^9*c.k,105898537895186+c.lower,105898921594081+c.upper)) = pointBounds31625 := by
 decide +kernel
def cuts31626 : List PrefixCut := [⟨70,223049747,223049868⟩,
⟨128,404987077,404987300⟩]
theorem checked31626 : checkPrefixCuts (2^48) 4149215233 9 Manual.Count131072.C031626.packed 128 cuts31626 = true := by
 decide +kernel
def pointBounds31626 : List (Nat × Nat × Nat) := [(4149286912,105899158278968,105899541978214)]
theorem point_links_checked31626 : (cuts31626.take 1).map (fun c => (4149215233-1+2*2^9*c.k,105898935229221+c.lower,105899318928346+c.upper)) = pointBounds31626 := by
 decide +kernel
def cuts31627 : List PrefixCut := [⟨69,214495480,214495606⟩,
⟨128,400497173,400497411⟩]
theorem checked31627 : checkPrefixCuts (2^48) 4149346305 9 Manual.Count131072.C031627.packed 128 cuts31627 = true := by
 decide +kernel
def pointBounds31627 : List (Nat × Nat × Nat) := [(4149416960,105899554711778,105899938411252)]
theorem point_links_checked31627 : (cuts31627.take 1).map (fun c => (4149346305-1+2*2^9*c.k,105899340216298+c.lower,105899723915646+c.upper)) = pointBounds31627 := by
 decide +kernel
def cuts31628 : List PrefixCut := [⟨68,216455893,216456014⟩,
⟨128,402858707,402858931⟩]
theorem checked31628 : checkPrefixCuts (2^48) 4149477377 9 Manual.Count131072.C031628.packed 128 cuts31628 = true := by
 decide +kernel
def pointBounds31628 : List (Nat × Nat × Nat) := [(4149547008,105899957169364,105900340869071)]
theorem point_links_checked31628 : (cuts31628.take 1).map (fun c => (4149477377-1+2*2^9*c.k,105899740713471+c.lower,105900124413057+c.upper)) = pointBounds31628 := by
 decide +kernel
def cuts31629 : List PrefixCut := [⟨67,214142818,214142938⟩,
⟨128,403592129,403592362⟩]
theorem checked31629 : checkPrefixCuts (2^48) 4149608449 9 Manual.Count131072.C031629.packed 128 cuts31629 = true := by
 decide +kernel
def pointBounds31629 : List (Nat × Nat × Nat) := [(4149677056,105900357714996,105900741414926)]
theorem point_links_checked31629 : (cuts31629.take 1).map (fun c => (4149608449-1+2*2^9*c.k,105900143572178+c.lower,105900527271988+c.upper)) = pointBounds31629 := by
 decide +kernel
def cuts31630 : List PrefixCut := [⟨66,204300868,204300984⟩,
⟨128,398288687,398288914⟩]
theorem checked31630 : checkPrefixCuts (2^48) 4149739521 9 Manual.Count131072.C031630.packed 128 cuts31630 = true := by
 decide +kernel
def pointBounds31630 : List (Nat × Nat × Nat) := [(4149807104,105900751465175,105901135165334)]
theorem point_links_checked31630 : (cuts31630.take 1).map (fun c => (4149739521-1+2*2^9*c.k,105900547164307+c.lower,105900930864350+c.upper)) = pointBounds31630 := by
 decide +kernel
def cuts31631 : List PrefixCut := [⟨65,206125783,206125900⟩,
⟨128,400310984,400311211⟩]
theorem checked31631 : checkPrefixCuts (2^48) 4149870593 9 Manual.Count131072.C031631.packed 128 cuts31631 = true := by
 decide +kernel
def pointBounds31631 : List (Nat × Nat × Nat) := [(4149937152,105901151578777,105901535279164)]
theorem point_links_checked31631 : (cuts31631.take 1).map (fun c => (4149870593-1+2*2^9*c.k,105900945452994+c.lower,105901329153264+c.upper)) = pointBounds31631 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000050
