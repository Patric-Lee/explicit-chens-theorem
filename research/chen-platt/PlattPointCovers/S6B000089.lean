import PlattPointSubsetKernel
import PlattPointPackets.S1B000600
import PlattPointPackets.S1B000601
import PlattPointPackets.S1B000602
import PlattPointPackets.S1B000603
import PlattPointPackets.S1B000604
import PlattGlobalGrid.S6B000089
namespace ChenEffective.PlattWindow.PointCovers.S6B000089
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000600.points ++ ChenEffective.PlattWindow.PointPackets.S1B000601.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000602.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000603.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000604.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000089.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000089.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000089
