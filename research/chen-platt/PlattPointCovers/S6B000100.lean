import PlattPointSubsetKernel
import PlattPointPackets.S2B000002
import PlattPointPackets.S2B000003
import PlattPointPackets.S2B000004
import PlattPointPackets.S2B000005
import PlattGlobalGrid.S6B000100
namespace ChenEffective.PlattWindow.PointCovers.S6B000100
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000002.points ++ ChenEffective.PlattWindow.PointPackets.S2B000003.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000004.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000005.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000100.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000100.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000100
