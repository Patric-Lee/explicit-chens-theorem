import PlattAssemblyKernel
import PlattCertificates.Count131072.C042528
import PlattCertificates.Count131072.C042529
import PlattCertificates.Count131072.C042530
import PlattCertificates.Count131072.C042531
import PlattCertificates.Count131072.C042532
import PlattCertificates.Count131072.C042533
import PlattCertificates.Count131072.C042534
import PlattCertificates.Count131072.C042535
import PlattCertificates.Count131072.C042536
import PlattCertificates.Count131072.C042537
import PlattCertificates.Count131072.C042538
import PlattCertificates.Count131072.C042539
import PlattCertificates.Count131072.C042540
import PlattCertificates.Count131072.C042541
import PlattCertificates.Count131072.C042542
import PlattCertificates.Count131072.C042543
import PlattCertificates.Count131072.C042544
import PlattCertificates.Count131072.C042545
import PlattCertificates.Count131072.C042546
import PlattCertificates.Count131072.C042547
import PlattCertificates.Count131072.C042548
import PlattCertificates.Count131072.C042549
import PlattCertificates.Count131072.C042550
import PlattCertificates.Count131072.C042551
import PlattCertificates.Count131072.C042552
import PlattCertificates.Count131072.C042553
import PlattCertificates.Count131072.C042554
import PlattCertificates.Count131072.C042555
import PlattCertificates.Count131072.C042556
import PlattCertificates.Count131072.C042557
import PlattCertificates.Count131072.C042558
import PlattCertificates.Count131072.C042559
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000079
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts42528 : List PrefixCut := [⟨48,219752012,219752138⟩,
⟨64,294633334,294633502⟩]
theorem checked42528 : checkPrefixCuts (2^48) 5578162177 10 Manual.Count131072.C042528.packed 64 cuts42528 = true := by
 decide +kernel
def pointBounds42528 : List (Nat × Nat × Nat) := [(5578260480,109635525457580,109635911416479)]
theorem point_links_checked42528 : (cuts42528.take 1).map (fun c => (5578162177-1+2*2^10*c.k,109635305705568+c.lower,109635691664341+c.upper)) = pointBounds42528 := by
 decide +kernel
def cuts42529 : List PrefixCut := [⟨64,295938332,295938508⟩]
theorem checked42529 : checkPrefixCuts (2^48) 5578293249 10 Manual.Count131072.C042529.packed 64 cuts42529 = true := by
 decide +kernel
def cuts42530 : List PrefixCut := [⟨6,27247170,27247187⟩,
⟨64,293913087,293913260⟩]
theorem checked42530 : checkPrefixCuts (2^48) 5578424321 10 Manual.Count131072.C042530.packed 64 cuts42530 = true := by
 decide +kernel
def pointBounds42530 : List (Nat × Nat × Nat) := [(5578436608,109635923524404,109636309483538)]
theorem point_links_checked42530 : (cuts42530.take 1).map (fun c => (5578424321-1+2*2^10*c.k,109635896277234+c.lower,109636282236351+c.upper)) = pointBounds42530 := by
 decide +kernel
def cuts42531 : List PrefixCut := [⟨28,128966399,128966474⟩,
⟨64,295621706,295621877⟩]
theorem checked42531 : checkPrefixCuts (2^48) 5578555393 10 Manual.Count131072.C042531.packed 64 cuts42531 = true := by
 decide +kernel
def pointBounds42531 : List (Nat × Nat × Nat) := [(5578612736,109636319156720,109636705116085)]
theorem point_links_checked42531 : (cuts42531.take 1).map (fun c => (5578555393-1+2*2^10*c.k,109636190190321+c.lower,109636576149611+c.upper)) = pointBounds42531 := by
 decide +kernel
def cuts42532 : List PrefixCut := [⟨50,233959583,233959717⟩,
⟨64,298238432,298238601⟩]
theorem checked42532 : checkPrefixCuts (2^48) 5578686465 10 Manual.Count131072.C042532.packed 64 cuts42532 = true := by
 decide +kernel
def pointBounds42532 : List (Nat × Nat × Nat) := [(5578788864,109636719771610,109637105731205)]
theorem point_links_checked42532 : (cuts42532.take 1).map (fun c => (5578686465-1+2*2^10*c.k,109636485812027+c.lower,109636871771488+c.upper)) = pointBounds42532 := by
 decide +kernel
def cuts42533 : List PrefixCut := [⟨64,298786379,298786555⟩]
theorem checked42533 : checkPrefixCuts (2^48) 5578817537 10 Manual.Count131072.C042533.packed 64 cuts42533 = true := by
 decide +kernel
def cuts42534 : List PrefixCut := [⟨8,36376584,36376606⟩,
⟨64,295449508,295449682⟩]
theorem checked42534 : checkPrefixCuts (2^48) 5578948609 10 Manual.Count131072.C042534.packed 64 cuts42534 = true := by
 decide +kernel
def pointBounds42534 : List (Nat × Nat × Nat) := [(5578964992,109637119213422,109637505173250)]
theorem point_links_checked42534 : (cuts42534.take 1).map (fun c => (5578948609-1+2*2^10*c.k,109637082836838+c.lower,109637468796644+c.upper)) = pointBounds42534 := by
 decide +kernel
def cuts42535 : List PrefixCut := [⟨30,140305822,140305903⟩,
⟨64,293979508,293979677⟩]
theorem checked42535 : checkPrefixCuts (2^48) 5579079681 10 Manual.Count131072.C042535.packed 64 cuts42535 = true := by
 decide +kernel
def pointBounds42535 : List (Nat × Nat × Nat) := [(5579141120,109637518592168,109637904552229)]
theorem point_links_checked42535 : (cuts42535.take 1).map (fun c => (5579079681-1+2*2^10*c.k,109637378286346+c.lower,109637764246326+c.upper)) = pointBounds42535 := by
 decide +kernel
def cuts42536 : List PrefixCut := [⟨52,240849194,240849332⟩,
⟨64,296747341,296747512⟩]
theorem checked42536 : checkPrefixCuts (2^48) 5579210753 10 Manual.Count131072.C042536.packed 64 cuts42536 = true := by
 decide +kernel
def pointBounds42536 : List (Nat × Nat × Nat) := [(5579317248,109637913115048,109638299075335)]
theorem point_links_checked42536 : (cuts42536.take 1).map (fun c => (5579210753-1+2*2^10*c.k,109637672265854+c.lower,109638058226003+c.upper)) = pointBounds42536 := by
 decide +kernel
def cuts42537 : List PrefixCut := [⟨64,295680957,295681130⟩]
theorem checked42537 : checkPrefixCuts (2^48) 5579341825 10 Manual.Count131072.C042537.packed 64 cuts42537 = true := by
 decide +kernel
def cuts42538 : List PrefixCut := [⟨10,46109659,46109686⟩,
⟨64,294463225,294463395⟩]
theorem checked42538 : checkPrefixCuts (2^48) 5579472897 10 Manual.Count131072.C042538.packed 64 cuts42538 = true := by
 decide +kernel
def pointBounds42538 : List (Nat × Nat × Nat) := [(5579493376,109638310803811,109638696764331)]
theorem point_links_checked42538 : (cuts42538.take 1).map (fun c => (5579472897-1+2*2^10*c.k,109638264694152+c.lower,109638650654645+c.upper)) = pointBounds42538 := by
 decide +kernel
def cuts42539 : List PrefixCut := [⟨32,144631015,144631099⟩,
⟨64,293800479,293800649⟩]
theorem checked42539 : checkPrefixCuts (2^48) 5579603969 10 Manual.Count131072.C042539.packed 64 cuts42539 = true := by
 decide +kernel
def pointBounds42539 : List (Nat × Nat × Nat) := [(5579669504,109638703788392,109639089749139)]
theorem point_links_checked42539 : (cuts42539.take 1).map (fun c => (5579603969-1+2*2^10*c.k,109638559157377+c.lower,109638945118040+c.upper)) = pointBounds42539 := by
 decide +kernel
def cuts42540 : List PrefixCut := [⟨54,254648515,254648665⟩,
⟨64,300654201,300654378⟩]
theorem checked42540 : checkPrefixCuts (2^48) 5579735041 10 Manual.Count131072.C042540.packed 64 cuts42540 = true := by
 decide +kernel
def pointBounds42540 : List (Nat × Nat × Nat) := [(5579845632,109639107606371,109639493567354)]
theorem point_links_checked42540 : (cuts42540.take 1).map (fun c => (5579735041-1+2*2^10*c.k,109638852957856+c.lower,109639238918689+c.upper)) = pointBounds42540 := by
 decide +kernel
def cuts42541 : List PrefixCut := [⟨64,293080477,293080649⟩]
theorem checked42541 : checkPrefixCuts (2^48) 5579866113 10 Manual.Count131072.C042541.packed 64 cuts42541 = true := by
 decide +kernel
def cuts42542 : List PrefixCut := [⟨12,57202867,57202900⟩,
⟨64,300640075,300640248⟩]
theorem checked42542 : checkPrefixCuts (2^48) 5579997185 10 Manual.Count131072.C042542.packed 64 cuts42542 = true := by
 decide +kernel
def pointBounds42542 : List (Nat × Nat × Nat) := [(5580021760,109639503895401,109639889856616)]
theorem point_links_checked42542 : (cuts42542.take 1).map (fun c => (5579997185-1+2*2^10*c.k,109639446692534+c.lower,109639832653716+c.upper)) = pointBounds42542 := by
 decide +kernel
def cuts42543 : List PrefixCut := [⟨34,156471265,156471358⟩,
⟨64,295588810,295588984⟩]
theorem checked42543 : checkPrefixCuts (2^48) 5580128257 10 Manual.Count131072.C042543.packed 64 cuts42543 = true := by
 decide +kernel
def pointBounds42543 : List (Nat × Nat × Nat) := [(5580197888,109639903803874,109640289765322)]
theorem point_links_checked42543 : (cuts42543.take 1).map (fun c => (5580128257-1+2*2^10*c.k,109639747332609+c.lower,109640133293964+c.upper)) = pointBounds42543 := by
 decide +kernel
def cuts42544 : List PrefixCut := [⟨56,257096099,257096251⟩,
⟨64,295430559,295430731⟩]
theorem checked42544 : checkPrefixCuts (2^48) 5580259329 10 Manual.Count131072.C042544.packed 64 cuts42544 = true := by
 decide +kernel
def pointBounds42544 : List (Nat × Nat × Nat) := [(5580374016,109640300017518,109640685979199)]
theorem point_links_checked42544 : (cuts42544.take 1).map (fun c => (5580259329-1+2*2^10*c.k,109640042921419+c.lower,109640428882948+c.upper)) = pointBounds42544 := by
 decide +kernel
def cuts42545 : List PrefixCut := [⟨64,291943289,291943457⟩]
theorem checked42545 : checkPrefixCuts (2^48) 5580390401 10 Manual.Count131072.C042545.packed 64 cuts42545 = true := by
 decide +kernel
def cuts42546 : List PrefixCut := [⟨14,65166782,65166821⟩,
⟨64,296627185,296627352⟩]
theorem checked42546 : checkPrefixCuts (2^48) 5580521473 10 Manual.Count131072.C042546.packed 64 cuts42546 = true := by
 decide +kernel
def pointBounds42546 : List (Nat × Nat × Nat) := [(5580550144,109640695462049,109641081423957)]
theorem point_links_checked42546 : (cuts42546.take 1).map (fun c => (5580521473-1+2*2^10*c.k,109640630295267+c.lower,109641016257136+c.upper)) = pointBounds42546 := by
 decide +kernel
def cuts42547 : List PrefixCut := [⟨36,165585656,165585748⟩,
⟨64,295661924,295662090⟩]
theorem checked42547 : checkPrefixCuts (2^48) 5580652545 10 Manual.Count131072.C042547.packed 64 cuts42547 = true := by
 decide +kernel
def pointBounds42547 : List (Nat × Nat × Nat) := [(5580726272,109641092508108,109641478470236)]
theorem point_links_checked42547 : (cuts42547.take 1).map (fun c => (5580652545-1+2*2^10*c.k,109640926922452+c.lower,109641312884488+c.upper)) = pointBounds42547 := by
 decide +kernel
def cuts42548 : List PrefixCut := [⟨58,269125993,269126149⟩,
⟨64,295806276,295806449⟩]
theorem checked42548 : checkPrefixCuts (2^48) 5580783617 10 Manual.Count131072.C042548.packed 64 cuts42548 = true := by
 decide +kernel
def pointBounds42548 : List (Nat × Nat × Nat) := [(5580902400,109641491710369,109641877672727)]
theorem point_links_checked42548 : (cuts42548.take 1).map (fun c => (5580783617-1+2*2^10*c.k,109641222584376+c.lower,109641608546578+c.upper)) = pointBounds42548 := by
 decide +kernel
def cuts42549 : List PrefixCut := [⟨64,294992389,294992563⟩]
theorem checked42549 : checkPrefixCuts (2^48) 5580914689 10 Manual.Count131072.C042549.packed 64 cuts42549 = true := by
 decide +kernel
def cuts42550 : List PrefixCut := [⟨16,75297860,75297904⟩,
⟨64,295439388,295439558⟩]
theorem checked42550 : checkPrefixCuts (2^48) 5581045761 10 Manual.Count131072.C042550.packed 64 cuts42550 = true := by
 decide +kernel
def pointBounds42550 : List (Nat × Nat × Nat) := [(5581078528,109641888680901,109642274643494)]
theorem point_links_checked42550 : (cuts42550.take 1).map (fun c => (5581045761-1+2*2^10*c.k,109641813383041+c.lower,109642199345590+c.upper)) = pointBounds42550 := by
 decide +kernel
def cuts42551 : List PrefixCut := [⟨38,173286205,173286303⟩,
⟨64,294827205,294827372⟩]
theorem checked42551 : checkPrefixCuts (2^48) 5581176833 10 Manual.Count131072.C042551.packed 64 cuts42551 = true := by
 decide +kernel
def pointBounds42551 : List (Nat × Nat × Nat) := [(5581254656,109642282108634,109642668071451)]
theorem point_links_checked42551 : (cuts42551.take 1).map (fun c => (5581176833-1+2*2^10*c.k,109642108822429+c.lower,109642494785148+c.upper)) = pointBounds42551 := by
 decide +kernel
def cuts42552 : List PrefixCut := [⟨60,275001080,275001236⟩,
⟨64,293357804,293357972⟩]
theorem checked42552 : checkPrefixCuts (2^48) 5581307905 10 Manual.Count131072.C042552.packed 64 cuts42552 = true := by
 decide +kernel
def pointBounds42552 : List (Nat × Nat × Nat) := [(5581430784,109642678650714,109643064613756)]
theorem point_links_checked42552 : (cuts42552.take 1).map (fun c => (5581307905-1+2*2^10*c.k,109642403649634+c.lower,109642789612520+c.upper)) = pointBounds42552 := by
 decide +kernel
def cuts42553 : List PrefixCut := [⟨64,296628837,296629009⟩]
theorem checked42553 : checkPrefixCuts (2^48) 5581438977 10 Manual.Count131072.C042553.packed 64 cuts42553 = true := by
 decide +kernel
def cuts42554 : List PrefixCut := [⟨18,81644838,81644886⟩,
⟨64,295764599,295764770⟩]
theorem checked42554 : checkPrefixCuts (2^48) 5581570049 10 Manual.Count131072.C042554.packed 64 cuts42554 = true := by
 decide +kernel
def pointBounds42554 : List (Nat × Nat × Nat) := [(5581606912,109643075281113,109643461244387)]
theorem point_links_checked42554 : (cuts42554.take 1).map (fun c => (5581570049-1+2*2^10*c.k,109642993636275+c.lower,109643379599501+c.upper)) = pointBounds42554 := by
 decide +kernel
def cuts42555 : List PrefixCut := [⟨40,184565702,184565811⟩,
⟨64,294244852,294245027⟩]
theorem checked42555 : checkPrefixCuts (2^48) 5581701121 10 Manual.Count131072.C042555.packed 64 cuts42555 = true := by
 decide +kernel
def pointBounds42555 : List (Nat × Nat × Nat) := [(5581783040,109643473966576,109643859930082)]
theorem point_links_checked42555 : (cuts42555.take 1).map (fun c => (5581701121-1+2*2^10*c.k,109643289400874+c.lower,109643675364271+c.upper)) = pointBounds42555 := by
 decide +kernel
def cuts42556 : List PrefixCut := [⟨62,282085265,282085433⟩,
⟨64,291111485,291111658⟩]
theorem checked42556 : checkPrefixCuts (2^48) 5581832193 10 Manual.Count131072.C042556.packed 64 cuts42556 = true := by
 decide +kernel
def pointBounds42556 : List (Nat × Nat × Nat) := [(5581959168,109643865730991,109644251694731)]
theorem point_links_checked42556 : (cuts42556.take 1).map (fun c => (5581832193-1+2*2^10*c.k,109643583645726+c.lower,109643969609298+c.upper)) = pointBounds42556 := by
 decide +kernel
def cuts42557 : List PrefixCut := [⟨64,292415727,292415909⟩]
theorem checked42557 : checkPrefixCuts (2^48) 5581963265 10 Manual.Count131072.C042557.packed 64 cuts42557 = true := by
 decide +kernel
def cuts42558 : List PrefixCut := [⟨20,92276688,92276741⟩,
⟨64,293114790,293114957⟩]
theorem checked42558 : checkPrefixCuts (2^48) 5582094337 10 Manual.Count131072.C042558.packed 64 cuts42558 = true := by
 decide +kernel
def pointBounds42558 : List (Nat × Nat × Nat) := [(5582135296,109644259449626,109644645413606)]
theorem point_links_checked42558 : (cuts42558.take 1).map (fun c => (5582094337-1+2*2^10*c.k,109644167172938+c.lower,109644553136865+c.upper)) = pointBounds42558 := by
 decide +kernel
def cuts42559 : List PrefixCut := [⟨42,191355418,191355534⟩,
⟨64,292956634,292956807⟩]
theorem checked42559 : checkPrefixCuts (2^48) 5582225409 10 Manual.Count131072.C042559.packed 64 cuts42559 = true := by
 decide +kernel
def pointBounds42559 : List (Nat × Nat × Nat) := [(5582311424,109644651643146,109645037607356)]
theorem point_links_checked42559 : (cuts42559.take 1).map (fun c => (5582225409-1+2*2^10*c.k,109644460287728+c.lower,109644846251822+c.upper)) = pointBounds42559 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000079
