import PlattAssemblyKernel
import PlattCertificates.Count131072.C018608
import PlattCertificates.Count131072.C018609
import PlattCertificates.Count131072.C018610
import PlattCertificates.Count131072.C018611
import PlattCertificates.Count131072.C018612
import PlattCertificates.Count131072.C018613
import PlattCertificates.Count131072.C018614
import PlattCertificates.Count131072.C018615
import PlattCertificates.Count131072.C018616
import PlattCertificates.Count131072.C018617
import PlattCertificates.Count131072.C018618
import PlattCertificates.Count131072.C018619
import PlattCertificates.Count131072.C018620
import PlattCertificates.Count131072.C018621
import PlattCertificates.Count131072.C018622
import PlattCertificates.Count131072.C018623
import PlattCertificates.Count131072.C018624
import PlattCertificates.Count131072.C018625
import PlattCertificates.Count131072.C018626
import PlattCertificates.Count131072.C018627
import PlattCertificates.Count131072.C018628
import PlattCertificates.Count131072.C018629
import PlattCertificates.Count131072.C018630
import PlattCertificates.Count131072.C018631
import PlattCertificates.Count131072.C018632
import PlattCertificates.Count131072.C018633
import PlattCertificates.Count131072.C018634
import PlattCertificates.Count131072.C018635
import PlattCertificates.Count131072.C018636
import PlattCertificates.Count131072.C018637
import PlattCertificates.Count131072.C018638
import PlattCertificates.Count131072.C018639
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000269
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18608 : List PrefixCut := [⟨53,289200677,289200851⟩,
⟨128,698564209,698564630⟩]
theorem checked18608 : checkPrefixCuts (2^48) 2442919937 9 Manual.Count131072.C018608.packed 128 cuts18608 = true := by
 decide +kernel
def pointBounds18608 : List (Nat × Nat × Nat) := [(2442974208,99084716946690,99085096759398),(2443051008,99085126310222,99085506123177)]
theorem point_links_checked18608 : (cuts18608.take 2).map (fun c => (2442919937-1+2*2^9*c.k,99084427746013+c.lower,99084807558547+c.upper)) = pointBounds18608 := by
 decide +kernel
def cuts18609 : List PrefixCut := [⟨75,402668345,402668596⟩,
⟨128,693111704,693112130⟩]
theorem checked18609 : checkPrefixCuts (2^48) 2443051009 9 Manual.Count131072.C018609.packed 128 cuts18609 = true := by
 decide +kernel
def pointBounds18609 : List (Nat × Nat × Nat) := [(2443127808,99085528978567,99085908791773)]
theorem point_links_checked18609 : (cuts18609.take 1).map (fun c => (2443051009-1+2*2^9*c.k,99085126310222+c.lower,99085506123177+c.upper)) = pointBounds18609 := by
 decide +kernel
def cuts18610 : List PrefixCut := [⟨22,119470478,119470549⟩,
⟨97,521307078,521307386⟩,
⟨128,689848901,689849312⟩]
theorem checked18610 : checkPrefixCuts (2^48) 2443182081 9 Manual.Count131072.C018610.packed 128 cuts18610 = true := by
 decide +kernel
def pointBounds18610 : List (Nat × Nat × Nat) := [(2443204608,99085938892404,99086318705856),(2443281408,99086340729004,99086720542693)]
theorem point_links_checked18610 : (cuts18610.take 2).map (fun c => (2443182081-1+2*2^9*c.k,99085819421926+c.lower,99086199235307+c.upper)) = pointBounds18610 := by
 decide +kernel
def cuts18611 : List PrefixCut := [⟨44,243189474,243189621⟩,
⟨119,650645490,650645881⟩,
⟨128,697530332,697530750⟩]
theorem checked18611 : checkPrefixCuts (2^48) 2443313153 9 Manual.Count131072.C018611.packed 128 cuts18611 = true := by
 decide +kernel
def pointBounds18611 : List (Nat × Nat × Nat) := [(2443358208,99086752460301,99087132274240),(2443435008,99087159916317,99087539730500)]
theorem point_links_checked18611 : (cuts18611.take 2).map (fun c => (2443313153-1+2*2^9*c.k,99086509270827+c.lower,99086889084619+c.upper)) = pointBounds18611 := by
 decide +kernel
def cuts18612 : List PrefixCut := [⟨66,361249480,361249697⟩,
⟨128,699566270,699566691⟩]
theorem checked18612 : checkPrefixCuts (2^48) 2443444225 9 Manual.Count131072.C018612.packed 128 cuts18612 = true := by
 decide +kernel
def pointBounds18612 : List (Nat × Nat × Nat) := [(2443511808,99087568050639,99087947865066)]
theorem point_links_checked18612 : (cuts18612.take 1).map (fun c => (2443444225-1+2*2^9*c.k,99087206801159+c.lower,99087586615369+c.upper)) = pointBounds18612 := by
 decide +kernel
def cuts18613 : List PrefixCut := [⟨13,67961785,67961825⟩,
⟨88,467201150,467201435⟩,
⟨128,687664386,687664802⟩]
theorem checked18613 : checkPrefixCuts (2^48) 2443575297 9 Manual.Count131072.C018613.packed 128 cuts18613 = true := by
 decide +kernel
def pointBounds18613 : List (Nat × Nat × Nat) := [(2443588608,99087974329214,99088354143885),(2443665408,99088373568579,99088753383495)]
theorem point_links_checked18613 : (cuts18613.take 2).map (fun c => (2443575297-1+2*2^9*c.k,99087906367429+c.lower,99088286182060+c.upper)) = pointBounds18613 := by
 decide +kernel
def cuts18614 : List PrefixCut := [⟨35,186020166,186020276⟩,
⟨110,600322985,600323338⟩,
⟨128,699030401,699030813⟩]
theorem checked18614 : checkPrefixCuts (2^48) 2443706369 9 Manual.Count131072.C018614.packed 128 cuts18614 = true := by
 decide +kernel
def pointBounds18614 : List (Nat × Nat × Nat) := [(2443742208,99088780051981,99089159867138),(2443819008,99089194354800,99089574170200)]
theorem point_links_checked18614 : (cuts18614.take 2).map (fun c => (2443706369-1+2*2^9*c.k,99088594031815+c.lower,99088973846862+c.upper)) = pointBounds18614 := by
 decide +kernel
def cuts18615 : List PrefixCut := [⟨57,311435970,311436160⟩,
⟨128,696689526,696689944⟩]
theorem checked18615 : checkPrefixCuts (2^48) 2443837441 9 Manual.Count131072.C018615.packed 128 cuts18615 = true := by
 decide +kernel
def pointBounds18615 : List (Nat × Nat × Nat) := [(2443895808,99089604498186,99089984313835)]
theorem point_links_checked18615 : (cuts18615.take 1).map (fun c => (2443837441-1+2*2^9*c.k,99089293062216+c.lower,99089672877675+c.upper)) = pointBounds18615 := by
 decide +kernel
def cuts18616 : List PrefixCut := [⟨4,23725257,23725270⟩,
⟨79,436491792,436492053⟩,
⟨128,704944272,704944691⟩]
theorem checked18616 : checkPrefixCuts (2^48) 2443968513 9 Manual.Count131072.C018616.packed 128 cuts18616 = true := by
 decide +kernel
def pointBounds18616 : List (Nat × Nat × Nat) := [(2443972608,99090013476999,99090393292889),(2444049408,99090426243534,99090806059672)]
theorem point_links_checked18616 : (cuts18616.take 2).map (fun c => (2443968513-1+2*2^9*c.k,99089989751742+c.lower,99090369567619+c.upper)) = pointBounds18616 := by
 decide +kernel
def cuts18617 : List PrefixCut := [⟨26,137851839,137851921⟩,
⟨101,546101207,546101533⟩,
⟨128,692468975,692469390⟩]
theorem checked18617 : checkPrefixCuts (2^48) 2444099585 9 Manual.Count131072.C018617.packed 128 cuts18617 = true := by
 decide +kernel
def pointBounds18617 : List (Nat × Nat × Nat) := [(2444126208,99090832547853,99091212364231),(2444203008,99091240797221,99091620613843)]
theorem point_links_checked18617 : (cuts18617.take 2).map (fun c => (2444099585-1+2*2^9*c.k,99090694696014+c.lower,99091074512310+c.upper)) = pointBounds18617 := by
 decide +kernel
def cuts18618 : List PrefixCut := [⟨48,264632464,264632616⟩,
⟨123,669286325,669286720⟩,
⟨128,696001783,696002194⟩]
theorem checked18618 : checkPrefixCuts (2^48) 2444230657 9 Manual.Count131072.C018618.packed 128 cuts18618 = true := by
 decide +kernel
def pointBounds18618 : List (Nat × Nat × Nat) := [(2444279808,99091651797453,99092031614316),(2444356608,99092056451314,99092436268420)]
theorem point_links_checked18618 : (cuts18618.take 2).map (fun c => (2444230657-1+2*2^9*c.k,99091387164989+c.lower,99091766981700+c.upper)) = pointBounds18618 := by
 decide +kernel
def cuts18619 : List PrefixCut := [⟨70,374816584,374816814⟩,
⟨128,693661229,693661648⟩]
theorem checked18619 : checkPrefixCuts (2^48) 2444361729 9 Manual.Count131072.C018619.packed 128 cuts18619 = true := by
 decide +kernel
def pointBounds18619 : List (Nat × Nat × Nat) := [(2444433408,99092457983356,99092837800708)]
theorem point_links_checked18619 : (cuts18619.take 1).map (fun c => (2444361729-1+2*2^9*c.k,99092083166772+c.lower,99092462983894+c.upper)) = pointBounds18619 := by
 decide +kernel
def cuts18620 : List PrefixCut := [⟨17,94995554,94995608⟩,
⟨92,515731431,515731738⟩,
⟨128,711126119,711126545⟩]
theorem checked18620 : checkPrefixCuts (2^48) 2444492801 9 Manual.Count131072.C018620.packed 128 cuts18620 = true := by
 decide +kernel
def pointBounds18620 : List (Nat × Nat × Nat) := [(2444510208,99092871823555,99093251641150),(2444587008,99093292559432,99093672377280)]
theorem point_links_checked18620 : (cuts18620.take 2).map (fun c => (2444492801-1+2*2^9*c.k,99092776828001+c.lower,99093156645542+c.upper)) = pointBounds18620 := by
 decide +kernel
def cuts18621 : List PrefixCut := [⟨39,209668882,209669008⟩,
⟨114,620246344,620246716⟩,
⟨128,696235141,696235559⟩]
theorem checked18621 : checkPrefixCuts (2^48) 2444623873 9 Manual.Count131072.C018621.packed 128 cuts18621 = true := by
 decide +kernel
def pointBounds18621 : List (Nat × Nat × Nat) := [(2444663808,99093697623002,99094077441095),(2444740608,99094108200464,99094488018803)]
theorem point_links_checked18621 : (cuts18621.take 2).map (fun c => (2444623873-1+2*2^9*c.k,99093487954120+c.lower,99093867772087+c.upper)) = pointBounds18621 := by
 decide +kernel
def cuts18622 : List PrefixCut := [⟨61,336763210,336763410⟩,
⟨128,701148570,701148990⟩]
theorem checked18622 : checkPrefixCuts (2^48) 2444754945 9 Manual.Count131072.C018622.packed 128 cuts18622 = true := by
 decide +kernel
def pointBounds18622 : List (Nat × Nat × Nat) := [(2444817408,99094520952471,99094900771056)]
theorem point_links_checked18622 : (cuts18622.take 1).map (fun c => (2444754945-1+2*2^9*c.k,99094184189261+c.lower,99094564007646+c.upper)) = pointBounds18622 := by
 decide +kernel
def cuts18623 : List PrefixCut := [⟨8,45820874,45820902⟩,
⟨83,452099892,452100172⟩,
⟨128,699844462,699844894⟩]
theorem checked18623 : checkPrefixCuts (2^48) 2444886017 9 Manual.Count131072.C018623.packed 128 cuts18623 = true := by
 decide +kernel
def pointBounds18623 : List (Nat × Nat × Nat) := [(2444894208,99094931158705,99095310977538),(2444971008,99095337437723,99095717256808)]
theorem point_links_checked18623 : (cuts18623.take 2).map (fun c => (2444886017-1+2*2^9*c.k,99094885337831+c.lower,99095265156636+c.upper)) = pointBounds18623 := by
 decide +kernel
def cuts18624 : List PrefixCut := [⟨30,163472018,163472117⟩,
⟨105,577783859,577784211⟩,
⟨128,703721008,703721436⟩]
theorem checked18624 : checkPrefixCuts (2^48) 2445017089 9 Manual.Count131072.C018624.packed 128 cuts18624 = true := by
 decide +kernel
def pointBounds18624 : List (Nat × Nat × Nat) := [(2445047808,99095748654311,99096128473647),(2445124608,99096162966152,99096542785741)]
theorem point_links_checked18624 : (cuts18624.take 2).map (fun c => (2445017089-1+2*2^9*c.k,99095585182293+c.lower,99095965001530+c.upper)) = pointBounds18624 := by
 decide +kernel
def cuts18625 : List PrefixCut := [⟨52,288246577,288246751⟩,
⟨127,700230129,700230549⟩,
⟨128,706215825,706216248⟩]
theorem checked18625 : checkPrefixCuts (2^48) 2445148161 9 Manual.Count131072.C018625.packed 128 cuts18625 = true := by
 decide +kernel
def pointBounds18625 : List (Nat × Nat × Nat) := [(2445201408,99096577149878,99096956969717),(2445278208,99096989133430,99097368953515)]
theorem point_links_checked18625 : (cuts18625.take 2).map (fun c => (2445148161-1+2*2^9*c.k,99096288903301+c.lower,99096668722966+c.upper)) = pointBounds18625 := by
 decide +kernel
def cuts18626 : List PrefixCut := [⟨74,404948953,404949194⟩,
⟨128,692825583,692825999⟩]
theorem checked18626 : checkPrefixCuts (2^48) 2445279233 9 Manual.Count131072.C018626.packed 128 cuts18626 = true := by
 decide +kernel
def pointBounds18626 : List (Nat × Nat × Nat) := [(2445355008,99097400068079,99097779888408)]
theorem point_links_checked18626 : (cuts18626.take 1).map (fun c => (2445279233-1+2*2^9*c.k,99096995119126+c.lower,99097374939214+c.upper)) = pointBounds18626 := by
 decide +kernel
def cuts18627 : List PrefixCut := [⟨21,113491390,113491459⟩,
⟨96,529119417,529119730⟩,
⟨128,707406104,707406525⟩]
theorem checked18627 : checkPrefixCuts (2^48) 2445410305 9 Manual.Count131072.C018627.packed 128 cuts18627 = true := by
 decide +kernel
def pointBounds18627 : List (Nat × Nat × Nat) := [(2445431808,99097801436099,99098181256672),(2445508608,99098217064126,99098596884943)]
theorem point_links_checked18627 : (cuts18627.take 2).map (fun c => (2445410305-1+2*2^9*c.k,99097687944709+c.lower,99098067765213+c.upper)) = pointBounds18627 := by
 decide +kernel
def cuts18628 : List PrefixCut := [⟨43,233299889,233300031⟩,
⟨118,633249111,633249494⟩,
⟨128,691715465,691715882⟩]
theorem checked18628 : checkPrefixCuts (2^48) 2445541377 9 Manual.Count131072.C018628.packed 128 cuts18628 = true := by
 decide +kernel
def pointBounds18628 : List (Nat × Nat × Nat) := [(2445585408,99098628650702,99099008471769),(2445662208,99099028599924,99099408421232)]
theorem point_links_checked18628 : (cuts18628.take 2).map (fun c => (2445541377-1+2*2^9*c.k,99098395350813+c.lower,99098775171738+c.upper)) = pointBounds18628 := by
 decide +kernel
def cuts18629 : List PrefixCut := [⟨65,357122512,357122725⟩,
⟨128,705949240,705949659⟩]
theorem checked18629 : checkPrefixCuts (2^48) 2445672449 9 Manual.Count131072.C018629.packed 128 cuts18629 = true := by
 decide +kernel
def pointBounds18629 : List (Nat × Nat × Nat) := [(2445739008,99099444188790,99099824010345)]
theorem point_links_checked18629 : (cuts18629.take 1).map (fun c => (2445672449-1+2*2^9*c.k,99099087066278+c.lower,99099466887620+c.upper)) = pointBounds18629 := by
 decide +kernel
def cuts18630 : List PrefixCut := [⟨12,65483101,65483140⟩,
⟨87,475291661,475291953⟩,
⟨128,700847795,700848221⟩]
theorem checked18630 : checkPrefixCuts (2^48) 2445803521 9 Manual.Count131072.C018630.packed 128 cuts18630 = true := by
 decide +kernel
def pointBounds18630 : List (Nat × Nat × Nat) := [(2445815808,99099858498619,99100238320419),(2445892608,99100268307179,99100648129232)]
theorem point_links_checked18630 : (cuts18630.take 2).map (fun c => (2445803521-1+2*2^9*c.k,99099793015518+c.lower,99100172837279+c.upper)) = pointBounds18630 := by
 decide +kernel
def cuts18631 : List PrefixCut := [⟨34,183664240,183664354⟩,
⟨109,596669233,596669599⟩,
⟨128,699084170,699084597⟩]
theorem checked18631 : checkPrefixCuts (2^48) 2445934593 9 Manual.Count131072.C018631.packed 128 cuts18631 = true := by
 decide +kernel
def pointBounds18631 : List (Nat × Nat × Nat) := [(2445969408,99100677527553,99101057349854),(2446046208,99101090532546,99101470355099)]
theorem point_links_checked18631 : (cuts18631.take 2).map (fun c => (2445934593-1+2*2^9*c.k,99100493863313+c.lower,99100873685500+c.upper)) = pointBounds18631 := by
 decide +kernel
def cuts18632 : List PrefixCut := [⟨56,302407009,302407191⟩,
⟨128,700082213,700082630⟩]
theorem checked18632 : checkPrefixCuts (2^48) 2446065665 9 Manual.Count131072.C018632.packed 128 cuts18632 = true := by
 decide +kernel
def pointBounds18632 : List (Nat × Nat × Nat) := [(2446123008,99101495354492,99101875177288)]
theorem point_links_checked18632 : (cuts18632.take 1).map (fun c => (2446065665-1+2*2^9*c.k,99101192947483+c.lower,99101572770097+c.upper)) = pointBounds18632 := by
 decide +kernel
def cuts18633 : List PrefixCut := [⟨3,17259939,17259949⟩,
⟨78,424242653,424242912⟩,
⟨128,688078389,688078807⟩]
theorem checked18633 : checkPrefixCuts (2^48) 2446196737 9 Manual.Count131072.C018633.packed 128 cuts18633 = true := by
 decide +kernel
def pointBounds18633 : List (Nat × Nat × Nat) := [(2446199808,99101910289635,99102290112676),(2446276608,99102317272349,99102697095639)]
theorem point_links_checked18633 : (cuts18633.take 2).map (fun c => (2446196737-1+2*2^9*c.k,99101893029696+c.lower,99102272852727+c.upper)) = pointBounds18633 := by
 decide +kernel
def cuts18634 : List PrefixCut := [⟨25,134159451,134159536⟩,
⟨100,541691924,541692250⟩,
⟨128,697821136,697821556⟩]
theorem checked18634 : checkPrefixCuts (2^48) 2446327809 9 Manual.Count131072.C018634.packed 128 cuts18634 = true := by
 decide +kernel
def pointBounds18634 : List (Nat × Nat × Nat) := [(2446353408,99102715267536,99103095091070),(2446430208,99103122800009,99103502623784)]
theorem point_links_checked18634 : (cuts18634.take 2).map (fun c => (2446327809-1+2*2^9*c.k,99102581108085+c.lower,99102960931534+c.upper)) = pointBounds18634 := by
 decide +kernel
def cuts18635 : List PrefixCut := [⟨47,258293708,258293866⟩,
⟨122,669367157,669367558⟩,
⟨128,702270881,702271300⟩]
theorem checked18635 : checkPrefixCuts (2^48) 2446458881 9 Manual.Count131072.C018635.packed 128 cuts18635 = true := by
 decide +kernel
def pointBounds18635 : List (Nat × Nat × Nat) := [(2446507008,99103537222929,99103917046956),(2446583808,99103948296378,99104328120648)]
theorem point_links_checked18635 : (cuts18635.take 2).map (fun c => (2446458881-1+2*2^9*c.k,99103278929221+c.lower,99103658753090+c.upper)) = pointBounds18635 := by
 decide +kernel
def cuts18636 : List PrefixCut := [⟨69,374360249,374360481⟩,
⟨128,698896814,698897235⟩]
theorem checked18636 : checkPrefixCuts (2^48) 2446589953 9 Manual.Count131072.C018636.packed 128 cuts18636 = true := by
 decide +kernel
def pointBounds18636 : List (Nat × Nat × Nat) := [(2446660608,99104355560351,99104735384871)]
theorem point_links_checked18636 : (cuts18636.take 1).map (fun c => (2446589953-1+2*2^9*c.k,99103981200102+c.lower,99104361024390+c.upper)) = pointBounds18636 := by
 decide +kernel
def cuts18637 : List PrefixCut := [⟨16,90997663,90997716⟩,
⟨91,492369101,492369388⟩,
⟨128,691267046,691267455⟩]
theorem checked18637 : checkPrefixCuts (2^48) 2446721025 9 Manual.Count131072.C018637.packed 128 cuts18637 = true := by
 decide +kernel
def pointBounds18637 : List (Nat × Nat × Nat) := [(2446737408,99104771094579,99105150919341),(2446814208,99105172466017,99105552291013)]
theorem point_links_checked18637 : (cuts18637.take 2).map (fun c => (2446721025-1+2*2^9*c.k,99104680096916+c.lower,99105059921625+c.upper)) = pointBounds18637 := by
 decide +kernel
def cuts18638 : List PrefixCut := [⟨38,208557710,208557835⟩,
⟨113,617035914,617036287⟩,
⟨128,698591984,698592407⟩]
theorem checked18638 : checkPrefixCuts (2^48) 2446852097 9 Manual.Count131072.C018638.packed 128 cuts18638 = true := by
 decide +kernel
def pointBounds18638 : List (Nat × Nat × Nat) := [(2446891008,99105579921672,99105959746915),(2446967808,99105988399876,99106368225367)]
theorem point_links_checked18638 : (cuts18638.take 2).map (fun c => (2446852097-1+2*2^9*c.k,99105371363962+c.lower,99105751189080+c.upper)) = pointBounds18638 := by
 decide +kernel
def cuts18639 : List PrefixCut := [⟨60,328749762,328749964⟩,
⟨128,684866553,684866966⟩]
theorem checked18639 : checkPrefixCuts (2^48) 2446983169 9 Manual.Count131072.C018639.packed 128 cuts18639 = true := by
 decide +kernel
def pointBounds18639 : List (Nat × Nat × Nat) := [(2447044608,99106398705708,99106778531451)]
theorem point_links_checked18639 : (cuts18639.take 1).map (fun c => (2446983169-1+2*2^9*c.k,99106069955946+c.lower,99106449781487+c.upper)) = pointBounds18639 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000269
