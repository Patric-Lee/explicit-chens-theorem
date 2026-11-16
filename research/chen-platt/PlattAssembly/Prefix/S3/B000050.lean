import PlattAssemblyKernel
import PlattCertificates.Count131072.C021600
import PlattCertificates.Count131072.C021601
import PlattCertificates.Count131072.C021602
import PlattCertificates.Count131072.C021603
import PlattCertificates.Count131072.C021604
import PlattCertificates.Count131072.C021605
import PlattCertificates.Count131072.C021606
import PlattCertificates.Count131072.C021607
import PlattCertificates.Count131072.C021608
import PlattCertificates.Count131072.C021609
import PlattCertificates.Count131072.C021610
import PlattCertificates.Count131072.C021611
import PlattCertificates.Count131072.C021612
import PlattCertificates.Count131072.C021613
import PlattCertificates.Count131072.C021614
import PlattCertificates.Count131072.C021615
import PlattCertificates.Count131072.C021616
import PlattCertificates.Count131072.C021617
import PlattCertificates.Count131072.C021618
import PlattCertificates.Count131072.C021619
import PlattCertificates.Count131072.C021620
import PlattCertificates.Count131072.C021621
import PlattCertificates.Count131072.C021622
import PlattCertificates.Count131072.C021623
import PlattCertificates.Count131072.C021624
import PlattCertificates.Count131072.C021625
import PlattCertificates.Count131072.C021626
import PlattCertificates.Count131072.C021627
import PlattCertificates.Count131072.C021628
import PlattCertificates.Count131072.C021629
import PlattCertificates.Count131072.C021630
import PlattCertificates.Count131072.C021631
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000050
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21600 : List PrefixCut := [⟨75,345399489,345399685⟩,
⟨128,590221456,590221793⟩]
theorem checked21600 : checkPrefixCuts (2^48) 2835087361 9 Manual.Count131072.C021600.packed 128 cuts21600 = true := by
 decide +kernel
def pointBounds21600 : List (Nat × Nat × Nat) := [(2835164160,101016740977346,101017121925887)]
theorem point_links_checked21600 : (cuts21600.take 1).map (fun c => (2835087361-1+2*2^9*c.k,101016395577857+c.lower,101016776526202+c.upper)) = pointBounds21600 := by
 decide +kernel
def cuts21601 : List PrefixCut := [⟨34,158148934,158149025⟩,
⟨121,569446289,569446614⟩,
⟨128,603397848,603398192⟩]
theorem checked21601 : checkPrefixCuts (2^48) 2835218433 9 Manual.Count131072.C021601.packed 128 cuts21601 = true := by
 decide +kernel
def pointBounds21601 : List (Nat × Nat × Nat) := [(2835253248,101017143948247,101017524897020),(2835342336,101017555245602,101017936194609)]
theorem point_links_checked21601 : (cuts21601.take 2).map (fun c => (2835218433-1+2*2^9*c.k,101016985799313+c.lower,101017366747995+c.upper)) = pointBounds21601 := by
 decide +kernel
def cuts21602 : List PrefixCut := [⟨80,369490411,369490627⟩,
⟨128,592152392,592152736⟩]
theorem checked21602 : checkPrefixCuts (2^48) 2835349505 9 Manual.Count131072.C021602.packed 128 cuts21602 = true := by
 decide +kernel
def pointBounds21602 : List (Nat × Nat × Nat) := [(2835431424,101017958687572,101018339636814)]
theorem point_links_checked21602 : (cuts21602.take 1).map (fun c => (2835349505-1+2*2^9*c.k,101017589197161+c.lower,101017970146187+c.upper)) = pointBounds21602 := by
 decide +kernel
def cuts21603 : List PrefixCut := [⟨39,185432898,185433000⟩,
⟨126,595401058,595401382⟩,
⟨128,603242937,603243267⟩]
theorem checked21603 : checkPrefixCuts (2^48) 2835480577 9 Manual.Count131072.C021603.packed 128 cuts21603 = true := by
 decide +kernel
def pointBounds21603 : List (Nat × Nat × Nat) := [(2835520512,101018366782451,101018747731923),(2835609600,101018776750611,101019157700305)]
theorem point_links_checked21603 : (cuts21603.take 2).map (fun c => (2835480577-1+2*2^9*c.k,101018181349553+c.lower,101018562298923+c.upper)) = pointBounds21603 := by
 decide +kernel
def cuts21604 : List PrefixCut := [⟨85,388017984,388018211⟩,
⟨128,590410031,590410374⟩]
theorem checked21604 : checkPrefixCuts (2^48) 2835611649 9 Manual.Count131072.C021604.packed 128 cuts21604 = true := by
 decide +kernel
def pointBounds21604 : List (Nat × Nat × Nat) := [(2835698688,101019172610474,101019553560401)]
theorem point_links_checked21604 : (cuts21604.take 1).map (fun c => (2835611649-1+2*2^9*c.k,101018784592490+c.lower,101019165542190+c.upper)) = pointBounds21604 := by
 decide +kernel
def cuts21605 : List PrefixCut := [⟨44,211619944,211620062⟩,
⟨128,596735530,596735868⟩]
theorem checked21605 : checkPrefixCuts (2^48) 2835742721 9 Manual.Count131072.C021605.packed 128 cuts21605 = true := by
 decide +kernel
def pointBounds21605 : List (Nat × Nat × Nat) := [(2835787776,101019586622465,101019967572626)]
theorem point_links_checked21605 : (cuts21605.take 1).map (fun c => (2835742721-1+2*2^9*c.k,101019375002521+c.lower,101019755952564+c.upper)) = pointBounds21605 := by
 decide +kernel
def cuts21606 : List PrefixCut := [⟨3,14987510,14987518⟩,
⟨90,414879492,414879727⟩,
⟨128,596906170,596906509⟩]
theorem checked21606 : checkPrefixCuts (2^48) 2835873793 9 Manual.Count131072.C021606.packed 128 cuts21606 = true := by
 decide +kernel
def pointBounds21606 : List (Nat × Nat × Nat) := [(2835876864,101019986725561,101020367675950),(2835965952,101020386617543,101020767568159)]
theorem point_links_checked21606 : (cuts21606.take 2).map (fun c => (2835873793-1+2*2^9*c.k,101019971738051+c.lower,101020352688432+c.upper)) = pointBounds21606 := by
 decide +kernel
def cuts21607 : List PrefixCut := [⟨49,228671107,228671235⟩,
⟨128,597970399,597970739⟩]
theorem checked21607 : checkPrefixCuts (2^48) 2836004865 9 Manual.Count131072.C021607.packed 128 cuts21607 = true := by
 decide +kernel
def pointBounds21607 : List (Nat × Nat × Nat) := [(2836055040,101020797315328,101021178266176)]
theorem point_links_checked21607 : (cuts21607.take 1).map (fun c => (2836004865-1+2*2^9*c.k,101020568644221+c.lower,101020949594941+c.upper)) = pointBounds21607 := by
 decide +kernel
def cuts21608 : List PrefixCut := [⟨8,37812638,37812660⟩,
⟨95,441835251,441835508⟩,
⟨128,597148862,597149209⟩]
theorem checked21608 : checkPrefixCuts (2^48) 2836135937 9 Manual.Count131072.C021608.packed 128 cuts21608 = true := by
 decide +kernel
def pointBounds21608 : List (Nat × Nat × Nat) := [(2836144128,101021204427258,101021585378340),(2836233216,101021608449871,101021989401188)]
theorem point_links_checked21608 : (cuts21608.take 2).map (fun c => (2836135937-1+2*2^9*c.k,101021166614620+c.lower,101021547565680+c.upper)) = pointBounds21608 := by
 decide +kernel
def cuts21609 : List PrefixCut := [⟨54,249490239,249490388⟩,
⟨128,598113574,598113921⟩]
theorem checked21609 : checkPrefixCuts (2^48) 2836267009 9 Manual.Count131072.C021609.packed 128 cuts21609 = true := by
 decide +kernel
def pointBounds21609 : List (Nat × Nat × Nat) := [(2836322304,101022013253721,101022394205277)]
theorem point_links_checked21609 : (cuts21609.take 1).map (fun c => (2836267009-1+2*2^9*c.k,101021763763482+c.lower,101022144714889+c.upper)) = pointBounds21609 := by
 decide +kernel
def cuts21610 : List PrefixCut := [⟨13,60633505,60633540⟩,
⟨100,471961329,471961604⟩,
⟨128,603444597,603444948⟩]
theorem checked21610 : checkPrefixCuts (2^48) 2836398081 9 Manual.Count131072.C021610.packed 128 cuts21610 = true := by
 decide +kernel
def pointBounds21610 : List (Nat × Nat × Nat) := [(2836411392,101022422510561,101022803462350),(2836500480,101022833838385,101023214790414)]
theorem point_links_checked21610 : (cuts21610.take 2).map (fun c => (2836398081-1+2*2^9*c.k,101022361877056+c.lower,101022742828810+c.upper)) = pointBounds21610 := by
 decide +kernel
def cuts21611 : List PrefixCut := [⟨59,277053208,277053366⟩,
⟨128,601035280,601035623⟩]
theorem checked21611 : checkPrefixCuts (2^48) 2836529153 9 Manual.Count131072.C021611.packed 128 cuts21611 = true := by
 decide +kernel
def pointBounds21611 : List (Nat × Nat × Nat) := [(2836589568,101023242374861,101023623327124)]
theorem point_links_checked21611 : (cuts21611.take 1).map (fun c => (2836529153-1+2*2^9*c.k,101022965321653+c.lower,101023346273758+c.upper)) = pointBounds21611 := by
 decide +kernel
def cuts21612 : List PrefixCut := [⟨18,86923068,86923117⟩,
⟨105,487297393,487297669⟩,
⟨128,593962545,593962888⟩]
theorem checked21612 : checkPrefixCuts (2^48) 2836660225 9 Manual.Count131072.C021612.packed 128 cuts21612 = true := by
 decide +kernel
def pointBounds21612 : List (Nat × Nat × Nat) := [(2836678656,101023653280001,101024034232498),(2836767744,101024053654326,101024434607050)]
theorem point_links_checked21612 : (cuts21612.take 2).map (fun c => (2836660225-1+2*2^9*c.k,101023566356933+c.lower,101023947309381+c.upper)) = pointBounds21612 := by
 decide +kernel
def cuts21613 : List PrefixCut := [⟨64,292803639,292803809⟩,
⟨128,596514675,596515023⟩]
theorem checked21613 : checkPrefixCuts (2^48) 2836791297 9 Manual.Count131072.C021613.packed 128 cuts21613 = true := by
 decide +kernel
def pointBounds21613 : List (Nat × Nat × Nat) := [(2836856832,101024453123117,101024834076078)]
theorem point_links_checked21613 : (cuts21613.take 1).map (fun c => (2836791297-1+2*2^9*c.k,101024160319478+c.lower,101024541272269+c.upper)) = pointBounds21613 := by
 decide +kernel
def cuts21614 : List PrefixCut := [⟨23,105865595,105865655⟩,
⟨110,512452797,512453094⟩,
⟨128,598669889,598670235⟩]
theorem checked21614 : checkPrefixCuts (2^48) 2836922369 9 Manual.Count131072.C021614.packed 128 cuts21614 = true := by
 decide +kernel
def pointBounds21614 : List (Nat × Nat × Nat) := [(2836945920,101024862699748,101025243652947),(2837035008,101025269286950,101025650240386)]
theorem point_links_checked21614 : (cuts21614.take 2).map (fun c => (2836922369-1+2*2^9*c.k,101024756834153+c.lower,101025137787292+c.upper)) = pointBounds21614 := by
 decide +kernel
def cuts21615 : List PrefixCut := [⟨69,318968399,318968585⟩,
⟨128,592689626,592689969⟩]
theorem checked21615 : checkPrefixCuts (2^48) 2837053441 9 Manual.Count131072.C021615.packed 128 cuts21615 = true := by
 decide +kernel
def pointBounds21615 : List (Nat × Nat × Nat) := [(2837124096,101025674472441,101026055426112)]
theorem point_links_checked21615 : (cuts21615.take 1).map (fun c => (2837053441-1+2*2^9*c.k,101025355504042+c.lower,101025736457527+c.upper)) = pointBounds21615 := by
 decide +kernel
def cuts21616 : List PrefixCut := [⟨28,137106483,137106558⟩,
⟨115,541869682,541869994⟩,
⟨128,601293402,601293749⟩]
theorem checked21616 : checkPrefixCuts (2^48) 2837184513 9 Manual.Count131072.C021616.packed 128 cuts21616 = true := by
 decide +kernel
def pointBounds21616 : List (Nat × Nat × Nat) := [(2837213184,101026085300151,101026466254054),(2837302272,101026490063350,101026871017490)]
theorem point_links_checked21616 : (cuts21616.take 2).map (fun c => (2837184513-1+2*2^9*c.k,101025948193668+c.lower,101026329147496+c.upper)) = pointBounds21616 := by
 decide +kernel
def cuts21617 : List PrefixCut := [⟨74,339374583,339374778⟩,
⟨128,591642815,591643152⟩]
theorem checked21617 : checkPrefixCuts (2^48) 2837315585 9 Manual.Count131072.C021617.packed 128 cuts21617 = true := by
 decide +kernel
def pointBounds21617 : List (Nat × Nat × Nat) := [(2837391360,101026888861653,101027269816023)]
theorem point_links_checked21617 : (cuts21617.take 1).map (fun c => (2837315585-1+2*2^9*c.k,101026549487070+c.lower,101026930441245+c.upper)) = pointBounds21617 := by
 decide +kernel
def cuts21618 : List PrefixCut := [⟨33,156536759,156536851⟩,
⟨120,561559430,561559755⟩,
⟨128,600047336,600047682⟩]
theorem checked21618 : checkPrefixCuts (2^48) 2837446657 9 Manual.Count131072.C021618.packed 128 cuts21618 = true := by
 decide +kernel
def pointBounds21618 : List (Nat × Nat × Nat) := [(2837480448,101027297666644,101027678621248),(2837569536,101027702689315,101028083644152)]
theorem point_links_checked21618 : (cuts21618.take 2).map (fun c => (2837446657-1+2*2^9*c.k,101027141129885+c.lower,101027522084397+c.upper)) = pointBounds21618 := by
 decide +kernel
def cuts21619 : List PrefixCut := [⟨79,368605222,368605437⟩,
⟨128,598134978,598135324⟩]
theorem checked21619 : checkPrefixCuts (2^48) 2837577729 9 Manual.Count131072.C021619.packed 128 cuts21619 = true := by
 decide +kernel
def pointBounds21619 : List (Nat × Nat × Nat) := [(2837658624,101028109782443,101028490737516)]
theorem point_links_checked21619 : (cuts21619.take 1).map (fun c => (2837577729-1+2*2^9*c.k,101027741177221+c.lower,101028122132079+c.upper)) = pointBounds21619 := by
 decide +kernel
def cuts21620 : List PrefixCut := [⟨38,178046440,178046542⟩,
⟨125,585014725,585015060⟩,
⟨128,600388613,600388956⟩]
theorem checked21620 : checkPrefixCuts (2^48) 2837708801 9 Manual.Count131072.C021620.packed 128 cuts21620 = true := by
 decide +kernel
def pointBounds21620 : List (Nat × Nat × Nat) := [(2837747712,101028517358639,101028898313945),(2837836800,101028924326924,101029305282463)]
theorem point_links_checked21620 : (cuts21620.take 2).map (fun c => (2837708801-1+2*2^9*c.k,101028339312199+c.lower,101028720267403+c.upper)) = pointBounds21620 := by
 decide +kernel
def cuts21621 : List PrefixCut := [⟨84,391780045,391780270⟩,
⟨128,593616500,593616845⟩]
theorem checked21621 : checkPrefixCuts (2^48) 2837839873 9 Manual.Count131072.C021621.packed 128 cuts21621 = true := by
 decide +kernel
def pointBounds21621 : List (Nat × Nat × Nat) := [(2837925888,101029331480857,101029712436629)]
theorem point_links_checked21621 : (cuts21621.take 1).map (fun c => (2837839873-1+2*2^9*c.k,101028939700812+c.lower,101029320656359+c.upper)) = pointBounds21621 := by
 decide +kernel
def cuts21622 : List PrefixCut := [⟨43,200841448,200841563⟩,
⟨128,596068474,596068817⟩]
theorem checked21622 : checkPrefixCuts (2^48) 2837970945 9 Manual.Count131072.C021622.packed 128 cuts21622 = true := by
 decide +kernel
def pointBounds21622 : List (Nat × Nat × Nat) := [(2838014976,101029734158760,101030115114767)]
theorem point_links_checked21622 : (cuts21622.take 1).map (fun c => (2837970945-1+2*2^9*c.k,101029533317312+c.lower,101029914273204+c.upper)) = pointBounds21622 := by
 decide +kernel
def cuts21623 : List PrefixCut := [⟨2,8826764,8826769⟩,
⟨89,413264566,413264810⟩,
⟨128,595049190,595049541⟩]
theorem checked21623 : checkPrefixCuts (2^48) 2838102017 9 Manual.Count131072.C021623.packed 128 cuts21623 = true := by
 decide +kernel
def pointBounds21623 : List (Nat × Nat × Nat) := [(2838104064,101030138212550,101030519168790),(2838193152,101030542650352,101030923606831)]
theorem point_links_checked21623 : (cuts21623.take 2).map (fun c => (2838102017-1+2*2^9*c.k,101030129385786+c.lower,101030510342021+c.upper)) = pointBounds21623 := by
 decide +kernel
def cuts21624 : List PrefixCut := [⟨48,220557914,220558039⟩,
⟨128,595418406,595418748⟩]
theorem checked21624 : checkPrefixCuts (2^48) 2838233089 9 Manual.Count131072.C021624.packed 128 cuts21624 = true := by
 decide +kernel
def pointBounds21624 : List (Nat × Nat × Nat) := [(2838282240,101030944992890,101031325949601)]
theorem point_links_checked21624 : (cuts21624.take 1).map (fun c => (2838233089-1+2*2^9*c.k,101030724434976+c.lower,101031105391562+c.upper)) = pointBounds21624 := by
 decide +kernel
def cuts21625 : List PrefixCut := [⟨7,33022902,33022921⟩,
⟨94,439901742,439901993⟩,
⟨128,601836614,601836960⟩]
theorem checked21625 : checkPrefixCuts (2^48) 2838364161 9 Manual.Count131072.C021625.packed 128 cuts21625 = true := by
 decide +kernel
def pointBounds21625 : List (Nat × Nat × Nat) := [(2838371328,101031352876284,101031733833231),(2838460416,101031759755124,101032140712303)]
theorem point_links_checked21625 : (cuts21625.take 2).map (fun c => (2838364161-1+2*2^9*c.k,101031319853382+c.lower,101031700810310+c.upper)) = pointBounds21625 := by
 decide +kernel
def cuts21626 : List PrefixCut := [⟨53,250980226,250980370⟩,
⟨128,602304731,602305075⟩]
theorem checked21626 : checkPrefixCuts (2^48) 2838495233 9 Manual.Count131072.C021626.packed 128 cuts21626 = true := by
 decide +kernel
def pointBounds21626 : List (Nat × Nat × Nat) := [(2838549504,101032172670222,101032553627640)]
theorem point_links_checked21626 : (cuts21626.take 1).map (fun c => (2838495233-1+2*2^9*c.k,101031921689996+c.lower,101032302647270+c.upper)) = pointBounds21626 := by
 decide +kernel
def cuts21627 : List PrefixCut := [⟨12,55627992,55628024⟩,
⟨99,457312361,457312623⟩,
⟨128,591369629,591369963⟩]
theorem checked21627 : checkPrefixCuts (2^48) 2838626305 9 Manual.Count131072.C021627.packed 128 cuts21627 = true := by
 decide +kernel
def pointBounds21627 : List (Nat × Nat × Nat) := [(2838638592,101032579622719,101032960580369),(2838727680,101032981307088,101033362264968)]
theorem point_links_checked21627 : (cuts21627.take 2).map (fun c => (2838626305-1+2*2^9*c.k,101032523994727+c.lower,101032904952345+c.upper)) = pointBounds21627 := by
 decide +kernel
def cuts21628 : List PrefixCut := [⟨58,274059511,274059666⟩,
⟨128,599968618,599968973⟩]
theorem checked21628 : checkPrefixCuts (2^48) 2838757377 9 Manual.Count131072.C021628.packed 128 cuts21628 = true := by
 decide +kernel
def pointBounds21628 : List (Nat × Nat × Nat) := [(2838816768,101033389423867,101033770381974)]
theorem point_links_checked21628 : (cuts21628.take 1).map (fun c => (2838757377-1+2*2^9*c.k,101033115364356+c.lower,101033496322308+c.upper)) = pointBounds21628 := by
 decide +kernel
def cuts21629 : List PrefixCut := [⟨17,78625456,78625502⟩,
⟨104,480470383,480470664⟩,
⟨128,592802270,592802614⟩]
theorem checked21629 : checkPrefixCuts (2^48) 2838888449 9 Manual.Count131072.C021629.packed 128 cuts21629 = true := by
 decide +kernel
def pointBounds21629 : List (Nat × Nat × Nat) := [(2838905856,101033793958430,101034174916783),(2838994944,101034195803357,101034576761945)]
theorem point_links_checked21629 : (cuts21629.take 2).map (fun c => (2838888449-1+2*2^9*c.k,101033715332974+c.lower,101034096291281+c.upper)) = pointBounds21629 := by
 decide +kernel
def cuts21630 : List PrefixCut := [⟨63,295250777,295250944⟩,
⟨128,595154404,595154753⟩]
theorem checked21630 : checkPrefixCuts (2^48) 2839019521 9 Manual.Count131072.C021630.packed 128 cuts21630 = true := by
 decide +kernel
def pointBounds21630 : List (Nat × Nat × Nat) := [(2839084032,101034603386021,101034984344839)]
theorem point_links_checked21630 : (cuts21630.take 1).map (fun c => (2839019521-1+2*2^9*c.k,101034308135244+c.lower,101034689093895+c.upper)) = pointBounds21630 := by
 decide +kernel
def cuts21631 : List PrefixCut := [⟨22,101321229,101321286⟩,
⟨109,512942984,512943272⟩,
⟨128,602264771,602265107⟩]
theorem checked21631 : checkPrefixCuts (2^48) 2839150593 9 Manual.Count131072.C021631.packed 128 cuts21631 = true := by
 decide +kernel
def pointBounds21631 : List (Nat × Nat × Nat) := [(2839173120,101035004610877,101035385569934),(2839262208,101035416232632,101035797191920)]
theorem point_links_checked21631 : (cuts21631.take 2).map (fun c => (2839150593-1+2*2^9*c.k,101034903289648+c.lower,101035284248648+c.upper)) = pointBounds21631 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000050
