import PlattPointSubsetKernel
import PlattPointPackets.S2B000049
import PlattPointPackets.S2B000050
import PlattPointPackets.S2B000051
import PlattPointPackets.S2B000052
import PlattGlobalGrid.S7B000000
namespace ChenEffective.PlattWindow.PointCovers.S7B000000
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000049.points ++ ChenEffective.PlattWindow.PointPackets.S2B000050.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000051.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000052.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000000.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000000.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000000
