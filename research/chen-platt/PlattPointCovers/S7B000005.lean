import PlattPointSubsetKernel
import PlattPointPackets.S2B000064
import PlattPointPackets.S2B000065
import PlattPointPackets.S2B000066
import PlattPointPackets.S2B000067
import PlattGlobalGrid.S7B000005
namespace ChenEffective.PlattWindow.PointCovers.S7B000005
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000064.points ++ ChenEffective.PlattWindow.PointPackets.S2B000065.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000066.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000067.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000005.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000005.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000005
